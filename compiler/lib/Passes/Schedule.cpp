//===- Schedule.cpp - the tau-schedule pass -------------------------------===//
//
// Decides when (Compiler 4): the cycle of every instruction, and with it
// which words wait in memory, and in which scratch words. Then gives every
// travelling word a stream of its own.
//
// The method is *list scheduling*, as in a textbook on compilers or on
// high-level synthesis: take the instructions one at a time, by priority,
// give each a cycle on which everything it needs is free, and never move it
// again. It is run in both directions and the shorter schedule is kept.
//
// What is scheduled. A *unit* is a set of instructions a fixed number of
// cycles apart: the instructions of one matrix product, or of one stored
// matrix, on consecutive cycles, and any other instruction alone. A read of a
// buffer word is not a unit. It is issued once for each instruction that
// uses its word, timed so that the word arrives on the cycle it is used;
// only a read that is pinned, or whose word is overwritten before it is
// used, is a unit of its own.
//
// What a unit waits for (its *dependences*):
//
//   * the units whose words it uses;
//   * for each word of memory, in the order of the placed program: a read
//     comes after the write before it, and a write after the reads and the
//     write before it;
//   * for the stored columns of a matrix slice, the same: a product that
//     uses them comes after they are installed and before they are replaced.
//
// The timing rule. A word issued at slice p is at slice q `lag` cycles later
// and on no other cycle (Machine 3.4). So a word goes *directly* from the
// unit that makes it to the unit that uses it only if the two are exactly
// that far apart. Otherwise it waits in memory: it is written to a scratch
// word of some memory slice on the cycle it gets there, and read back so as
// to arrive on time. That costs two instructions, which is why the
// priorities below try first of all to make words arrive exactly.
//
// A word is given its way when both its ends have a cycle. Until then the end
// that has one holds a slot on the nearest memory slice, in case the word
// has to wait: a write for the unit that makes the word, a read for a unit
// that uses it.
//
// Forward. Walk the cycles upward from 0. A unit is ready when everything it
// waits for has a cycle. On each cycle the ready units are tried in this
// order, and each one that fits is given the cycle:
//
//   1. a unit one of whose words arrives exactly now;
//   2. the unit with the longest path to the end of the program (*height*);
//   3. the unit that comes first in the program.
//
// Backward. Walk the cycles downward. A unit is ready when everything that
// waits for it has a cycle. The order is the mirror image: a unit whose word,
// issued now, arrives exactly when it is used; then the longest path from
// the start (*depth*); then program order. A store goes with the unit that
// makes its word, on the first cycle it fits. At the end every cycle is
// moved so that the first is 0.
//
// A forward walk is weak where two words meet (it fixes the first before it
// knows when the second comes) and a backward walk where one word parts.
// Neither is shorter on every program, so both are run.
//
// Pins. A pinned instruction is given its cycle before any walk. A word goes
// into it directly only from a unit exactly `lag` cycles before it. So the
// units whose words have to reach a pinned instruction are walked backward
// from the pins, each as late as it can be, together with whatever stands
// between one of them and a pinned instruction. Everything else is walked
// forward. A program with a pin is scheduled this one way: its cycles count
// from 0 and cannot be moved at the end.
//
// When one memory slice would have to issue two words for one instruction
// on one cycle, one of them goes round: it is read earlier, written to a
// scratch word of a second memory slice, and read from there.
//
// The pass refuses a program whose pins it cannot meet, or for which neither
// walk finds a schedule.
//
// Last, every word is put on a stream of its own, going towards its users,
// and the machine recorded on the function is widened to have as many
// streams as that takes (Compiler 4). So the cycles can be checked before
// any stream is shared. The machine's own number of streams is kept in
// `tau.streams` for `tau-route`, which fits the words onto them.
//
// Nothing here is proved. `tau-check placed.json scheduled.json` decides
// whether the timed instructions compute what the placed program computes
// and meet its pins, and `tau-check --decides` whether the pass kept to
// deciding when.
//
// Terms to look up: list scheduling, ASAP and ALAP schedules, critical path,
// spilling.
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Machine.h"
#include "tau/OpUtils.h"
#include "tau/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/Pass/Pass.h"
#include "llvm/ADT/DenseMap.h"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <limits>
#include <map>
#include <optional>
#include <set>

using namespace llvm;
using namespace mlir;

namespace {

using Cycle = int64_t;

//===----------------------------------------------------------------------===//
// The program to schedule
//===----------------------------------------------------------------------===//

/// One instruction of the placed program.
struct Instr {
  Operation *op;
  int slice;
  /// The cycles its result spends inside its slice, if it has a result.
  int delay = 0;
  bool hasResult = false;
  /// Its unit, and its cycle counted from the unit's. -1 for a read that is
  /// issued once for each user.
  int unit = -1;
  int offset = 0;
  /// For a read or a write: the contents of the word of memory it reads or
  /// makes (`Version`).
  int version = -1;
};

/// What one word of memory holds between two writes to it.
struct Version {
  int slice;
  int64_t addr;
  /// The unit of the write that makes these contents, or -1 for what the
  /// word holds at the start. And the place of that write in the program.
  int store = -1;
  size_t written = 0;
  /// The contents before and after, or -1.
  int prev = -1;
  int next = -1;
};

/// A word a unit uses.
struct Operand {
  /// The cycle of the unit on which the word is used, and the slice that
  /// uses it.
  int offset;
  int slice;
  /// Where the word comes from: the unit that makes it, or a word of memory.
  int producer = -1;
  int version = -1;
  /// Every place the instruction names the word.
  std::vector<OpOperand *> uses;
};

/// One unit use of a word: a unit and the number of its operand.
struct User {
  int unit;
  int operand;
};

struct Unit {
  std::vector<int> instrs;
  int length = 1;
  /// Its place in the program, for ties.
  size_t order = 0;
  std::vector<Operand> operands;
  /// The instruction that issues its word, or -1, and the users of the word.
  int result = -1;
  std::vector<User> users;
  /// The units it waits for and the units that wait for it, each with the
  /// least number of cycles between the two.
  std::vector<std::pair<int, Cycle>> preds, succs;
  /// The cycle a pin gives it.
  std::optional<Cycle> pin;
  Operation *pinned = nullptr;
  /// A write to a buffer, and the unit whose word it stores, or -1.
  bool isStore = false;
  int stores = -1;
  /// For such a store: whether it waits for that unit only as the user of
  /// its word, and not through other units as well. A backward walk can
  /// then place it together with the unit.
  bool together = false;
  /// The longest path from the start of the program and to its end.
  Cycle depth = 0;
  Cycle height = 0;
};

//===----------------------------------------------------------------------===//
// A schedule in the making
//===----------------------------------------------------------------------===//

/// Who has a slot of a slice.
struct Owner {
  /// `Fixed`: an instruction of `unit`. `Write`: held for the word of
  /// `unit`, in case it has to wait. `Read`: held for operand `operand` of
  /// `unit`, in case its word has waited.
  enum Kind { Fixed, Write, Read } kind;
  int unit;
  int operand = -1;
};

using Slots = std::map<std::pair<int, Cycle>, Owner>;

/// A slot of a memory slice.
struct Hold {
  int mem;
  Cycle cycle;
};

/// How an operand gets its word.
struct Delivery {
  enum How {
    None,    // not decided: the unit that makes the word has no cycle yet
    Direct,  // from the stream, as issued
    Scratch, // from the scratch word the word waits in, read on `read`
    Load,    // from its buffer word, read on `read`
    Via      // through a second memory slice
  } how = None;
  Cycle read = 0;
  /// `Via`: the word is read from where it is on `first`, written to a
  /// scratch word of `mem` on `write`, and read from there on `read`.
  int mem = -1;
  Cycle first = 0;
  Cycle write = 0;
  /// The read slot held while the word's way is not decided.
  std::optional<Hold> held;
};

struct Schedule {
  /// The cycle of each unit.
  std::vector<std::optional<Cycle>> time;
  /// For the word of each unit: the scratch write if it waits, and the write
  /// slot held while that is not decided.
  std::vector<std::optional<Hold>> wait, heldWrite;
  std::vector<std::vector<Delivery>> delivery;
  /// The cycle slots and the leaving slots that are taken (Machine 3.3 and
  /// 3.4).
  Slots issue, exit;
  /// For each `Version`, the cycles on which it is read.
  std::vector<std::vector<Cycle>> reads;
  size_t placed = 0;
  /// No slot is taken before `low` or after `high`.
  Cycle low = 0;
  Cycle high = 0;
};

/// Why a unit could not be given a cycle.
struct Why {
  enum Kind { Nothing, Busy, Leaving, TooEarly, Order, NoWay, NoMemory } kind =
      Nothing;
  int slice = 0;
  Cycle cycle = 0;
  int other = -1;
};

class Scheduler {
public:
  Scheduler(func::FuncOp func, const tau::Machine &machine)
      : func(func), machine(machine) {}

  /// False if no schedule was found; the error has been reported.
  bool run();

private:
  func::FuncOp func;
  const tau::Machine &machine;

  std::vector<Instr> instrs;
  std::vector<Unit> units;
  std::vector<Version> versions;
  std::vector<int> mems;
  /// For each position, the memory slices from the nearest on.
  std::vector<std::vector<int>> near;
  /// The reads that are issued once for each user, to be removed at the end.
  std::vector<Operation *> perUser;
  bool hasPins = false;

  Schedule st;
  /// With pins, cycles count from 0 and nothing may be issued before it.
  bool walled = false;
  std::vector<std::function<void()>> undo;
  Why why;

  // Building the program.
  bool build();
  void edge(int from, int to, Cycle lag);

  // The timing rule.
  int readDelay(int mem) const { return machine.delayOf(mem, "read"); }
  /// Machine 3.4: how many cycles after an instruction with this delay is
  /// issued at slice `p` its word can be used at slice `q`.
  static Cycle lag(int delay, int p, int q) {
    return delay + 1 + std::abs(q - p);
  }
  Cycle readLag(int mem, int q) const { return lag(readDelay(mem), mem, q); }
  /// The cycle on which the word of unit `p`, issued when the unit is on
  /// cycle `time`, is at `slice`.
  Cycle lands(int p, Cycle time, int slice) const {
    const Instr &result = instrs[units[p].result];
    return time + result.offset + lag(result.delay, result.slice, slice);
  }
  Cycle lands(int p, int slice) const { return lands(p, *st.time[p], slice); }
  /// The cycle on which unit `x` uses its operand `k`.
  Cycle uses(int x, int k) const {
    return *st.time[x] + units[x].operands[k].offset;
  }

  // Changing the schedule, so that a change can be taken back.
  template <typename T> void set(T &slot, T value) {
    undo.push_back([&slot, old = slot] { slot = old; });
    slot = std::move(value);
  }
  void rollback(size_t mark) {
    while (undo.size() > mark) {
      undo.back()();
      undo.pop_back();
    }
  }
  const Owner *owner(const Slots &slots, int slice, Cycle cycle) const {
    auto found = slots.find({slice, cycle});
    return found == slots.end() ? nullptr : &found->second;
  }
  void take(Slots &slots, int slice, Cycle cycle, Owner who) {
    undo.push_back([this, &slots, slice, cycle, low = st.low, high = st.high] {
      slots.erase({slice, cycle});
      st.low = low;
      st.high = high;
    });
    slots.insert({{slice, cycle}, who});
    st.low = std::min(st.low, cycle);
    st.high = std::max(st.high, cycle);
  }
  void drop(Slots &slots, int slice, Cycle cycle) {
    Owner who = slots.at({slice, cycle});
    slots.erase({slice, cycle});
    undo.push_back(
        [&slots, slice, cycle, who] { slots.insert({{slice, cycle}, who}); });
  }
  bool fail(Why::Kind kind, int slice = 0, Cycle cycle = 0, int other = -1) {
    why = {kind, slice, cycle, other};
    return false;
  }

  // Reads and writes of memory.
  bool readFree(int mem, Cycle cycle, const Owner *mine = nullptr);
  void takeRead(int mem, Cycle cycle, int unit);
  bool holdsWrite(int p, int mem, Cycle cycle) const;
  void releaseRead(int x, int k);
  void releaseWrite(int p);
  void holdRead(int x, int k);
  bool holdWrite(int p);
  bool inOrder(int version, Cycle cycle, bool write);

  // Giving a word its way.
  std::optional<Cycle> scratchRead(int x, int k, int mem, Cycle written);
  bool viaSecond(int x, int k, int from, Cycle after, int version);
  bool readWord(int x, int k);
  bool routeOne(int p, int x, int k);
  bool routeProducer(int p, const std::vector<User> &placed);

  // Giving a unit a cycle.
  bool place(int u, Cycle time);
  bool tryPlace(int u, Cycle time);
  bool tryWithStores(int u, Cycle time);

  // The walks.
  bool arrivesNow(int u, Cycle time) const;
  bool wantedNow(int u, Cycle time) const;
  bool storeGoesWith(int s, const std::vector<bool> &chosen) const;
  /// No cycle: later than any.
  static constexpr Cycle never = std::numeric_limits<Cycle>::max();
  std::vector<Cycle> latest() const;
  int pinAfter(int u) const;
  bool tooLate(int u, StringRef what);
  bool forward(Cycle from);
  bool backward(const std::vector<bool> &chosen, Cycle from, bool wall);
  bool pins();
  void reset();
  /// A unit that finds no cycle this far beyond every slot that is taken
  /// will find none further on: nothing it meets there changes any more. The
  /// distance covers the longest way a word is sent round through memory.
  Cycle beyond() const {
    return 2 * (64 + machine.maxDelay() + 1 +
                static_cast<Cycle>(machine.kinds.size()));
  }
  Cycle first(const Schedule &s) const;
  Cycle last(const Schedule &s) const;
  size_t waits(const Schedule &s) const;

  // Reporting. A walk that finds no schedule says why here; the pass
  // reports it if no walk finds one.
  struct Refusal {
    Operation *op = nullptr;
    std::string message;
    Operation *noted = nullptr;
    std::string note;
  };
  Refusal refusal;
  std::string describe(const Why &w) const;
  bool refuse(Operation *op, const Twine &message, Operation *noted = nullptr,
              const Twine &note = "");
  bool stuck(int u);
  void report();

  void write();
};

//===----------------------------------------------------------------------===//
// Building the program
//===----------------------------------------------------------------------===//

void Scheduler::edge(int from, int to, Cycle lag) {
  // A store of a word read from the address it writes waits for itself only
  // in name: its read is before its write on any cycle.
  if (from == to)
    return;
  for (auto &succ : units[from].succs)
    if (succ.first == to) {
      succ.second = std::max(succ.second, lag);
      for (auto &pred : units[to].preds)
        if (pred.first == from)
          pred.second = succ.second;
      return;
    }
  units[from].succs.push_back({to, lag});
  units[to].preds.push_back({from, lag});
}

bool Scheduler::build() {
  int positions = static_cast<int>(machine.kinds.size());
  for (int p = 0; p < positions; ++p)
    if (machine.kinds[p] == "mem")
      mems.push_back(p);
  near.resize(positions);
  for (int p = 0; p < positions; ++p) {
    near[p] = mems;
    std::stable_sort(near[p].begin(), near[p].end(), [p](int a, int b) {
      return std::abs(a - p) < std::abs(b - p);
    });
  }

  // The instructions, and what each word of memory holds when.
  llvm::DenseMap<Operation *, int> index;
  std::map<std::pair<int, int64_t>, int> current;
  for (Operation &op : func.getBody().front()) {
    if (!tau::isInstr(op))
      continue;
    Instr in;
    in.op = &op;
    in.slice = static_cast<int>(tau::intAttr(op, "slice"));
    in.hasResult = static_cast<bool>(tau::streamResult(op));
    in.delay = machine.delayOf(in.slice, tau::delayName(op));
    StringRef name = tau::instrName(op);
    if (name == "read" || name == "write") {
      std::pair<int, int64_t> word{in.slice, tau::intAttr(op, "addr")};
      auto found = current.find(word);
      if (found == current.end()) {
        versions.push_back({word.first, word.second});
        found = current.insert({word, versions.size() - 1}).first;
      }
      if (name == "write") {
        Version next{word.first, word.second};
        next.prev = found->second;
        next.written = instrs.size();
        versions[found->second].next = static_cast<int>(versions.size());
        found->second = static_cast<int>(versions.size());
        versions.push_back(next);
      }
      in.version = found->second;
    }
    index[&op] = static_cast<int>(instrs.size());
    instrs.push_back(in);
  }

  // The units. The instructions of one matrix product, or of one stored
  // matrix, are joined by the state they pass on and go on consecutive
  // cycles. A read is a unit only if it is pinned or its word is overwritten
  // before a user takes it.
  for (size_t i = 0; i < instrs.size(); ++i) {
    Instr &in = instrs[i];
    Operation *op = in.op;
    int state = -1;
    for (Value operand : op->getOperands())
      if (isa<tau::AccType>(operand.getType()))
        state = index.lookup(operand.getDefiningOp());
    if (state >= 0) {
      in.unit = instrs[state].unit;
      in.offset = instrs[state].offset + 1;
      units[in.unit].instrs.push_back(static_cast<int>(i));
      units[in.unit].length = in.offset + 1;
    } else {
      if (tau::instrName(*op) == "read") {
        bool own = static_cast<bool>(tau::optIntAttr(*op, "pin"));
        int next = versions[in.version].next;
        for (Operation *user : op->getResult(0).getUsers())
          own |= next >= 0 &&
                 versions[next].written < static_cast<size_t>(index.lookup(user));
        if (!own) {
          perUser.push_back(op);
          continue;
        }
      }
      in.unit = static_cast<int>(units.size());
      units.emplace_back();
      units.back().instrs.push_back(static_cast<int>(i));
      units.back().order = i;
    }
    Unit &unit = units[in.unit];
    if (in.hasResult)
      unit.result = static_cast<int>(i);
    if (tau::instrName(*op) == "write") {
      unit.isStore = true;
      versions[in.version].store = in.unit;
    }
    if (std::optional<int64_t> pin = tau::optIntAttr(*op, "pin")) {
      hasPins = true;
      if (unit.pin && *unit.pin != *pin - in.offset) {
        op->emitError("pinned to cycle ")
            << *pin << ", but another pin of the same product puts it on cycle "
            << *unit.pin + in.offset;
        return false;
      }
      if (*pin < in.offset) {
        op->emitError("pinned to cycle ")
            << *pin << ", but it cannot be issued before cycle " << in.offset;
        return false;
      }
      unit.pin = *pin - in.offset;
      unit.pinned = op;
    }
  }

  // The words each unit uses. An instruction that names one word twice, or
  // two reads of the same contents, uses it once.
  for (size_t u = 0; u < units.size(); ++u)
    for (int i : units[u].instrs) {
      const Instr &in = instrs[i];
      for (OpOperand &use : in.op->getOpOperands()) {
        if (!isa<tau::WordType>(use.get().getType()))
          continue;
        const Instr &source = instrs[index.lookup(use.get().getDefiningOp())];
        Operand operand{in.offset, in.slice};
        if (source.unit >= 0)
          operand.producer = source.unit;
        else
          operand.version = source.version;
        auto same = llvm::find_if(units[u].operands, [&](const Operand &o) {
          return o.offset == operand.offset && o.slice == operand.slice &&
                 o.producer == operand.producer && o.version == operand.version;
        });
        if (same != units[u].operands.end()) {
          same->uses.push_back(&use);
          continue;
        }
        operand.uses.push_back(&use);
        if (operand.producer >= 0)
          units[operand.producer].users.push_back(
              {static_cast<int>(u),
               static_cast<int>(units[u].operands.size())});
        units[u].operands.push_back(std::move(operand));
      }
    }
  for (size_t u = 0; u < units.size(); ++u)
    if (units[u].isStore && units[u].operands[0].producer >= 0)
      units[u].stores = units[u].operands[0].producer;

  // The dependences. First the words.
  for (size_t u = 0; u < units.size(); ++u)
    for (const Operand &operand : units[u].operands) {
      int me = static_cast<int>(u);
      if (operand.producer >= 0) {
        edge(operand.producer, me,
             lands(operand.producer, 0, operand.slice) - operand.offset);
        continue;
      }
      // A read for this unit: after the write before it, before the next.
      const Version &version = versions[operand.version];
      Cycle read = operand.offset - readLag(version.slice, operand.slice);
      if (version.store >= 0)
        edge(version.store, me, 1 - read);
      if (version.next >= 0)
        edge(me, versions[version.next].store, read + 1);
    }
  // Reads that are units, and the writes of each word in order.
  for (size_t u = 0; u < units.size(); ++u) {
    const Instr &in = instrs[units[u].instrs[0]];
    if (in.version < 0)
      continue;
    const Version &version = versions[in.version];
    if (units[u].isStore) {
      if (version.prev >= 0 && versions[version.prev].store >= 0)
        edge(versions[version.prev].store, static_cast<int>(u), 1);
    } else {
      if (version.store >= 0)
        edge(version.store, static_cast<int>(u), 1);
      if (version.next >= 0)
        edge(static_cast<int>(u), versions[version.next].store, 1);
    }
  }
  // The stored columns of each matrix slice: installing them is a write and
  // a product that uses them is a read.
  std::map<int, int> installed;
  std::map<int, std::vector<int>> since;
  for (size_t u = 0; u < units.size(); ++u) {
    int slice = instrs[units[u].instrs[0]].slice;
    bool installs = false, usesStored = false;
    for (int i : units[u].instrs) {
      installs |= tau::instrName(*instrs[i].op) == "install";
      usesStored |= tau::instrName(*instrs[i].op) == "macw";
    }
    int me = static_cast<int>(u);
    if (usesStored) {
      if (installed.count(slice))
        edge(installed[slice], me, units[installed[slice]].length);
      since[slice].push_back(me);
    }
    if (installs) {
      for (int product : since[slice])
        edge(product, me, units[product].length);
      if (installed.count(slice))
        edge(installed[slice], me, units[installed[slice]].length);
      installed[slice] = me;
      since[slice].clear();
    }
  }

  // A store waits for the unit that makes its word. If it also waits for
  // something else that waits for that unit, the two cannot be placed
  // together.
  for (size_t u = 0; u < units.size(); ++u) {
    Unit &store = units[u];
    if (store.stores < 0)
      continue;
    store.together = true;
    std::vector<int> todo{store.stores};
    std::set<int> seen;
    while (!todo.empty() && store.together) {
      int next = todo.back();
      todo.pop_back();
      for (auto [succ, lag] : units[next].succs) {
        if (succ == static_cast<int>(u))
          store.together &= next == store.stores;
        else if (static_cast<size_t>(succ) < u && seen.insert(succ).second)
          todo.push_back(succ);
      }
    }
  }

  // Depth and height: the longest paths, with every word going directly.
  // Units are in program order, and every dependence goes forward in it.
  for (size_t u = 0; u < units.size(); ++u) {
    Unit &unit = units[u];
    for (const Operand &operand : unit.operands)
      if (operand.version >= 0)
        unit.depth = std::max<Cycle>(
            unit.depth,
            readLag(versions[operand.version].slice, operand.slice) -
                operand.offset);
    for (auto [pred, lag] : unit.preds) {
      if (static_cast<size_t>(pred) >= u) {
        instrs[unit.instrs[0]].op->emitError(
            "this instruction waits for one that comes after it");
        return false;
      }
      unit.depth = std::max(unit.depth, units[pred].depth + lag);
    }
  }
  for (size_t u = units.size(); u-- > 0;)
    for (auto [succ, lag] : units[u].succs)
      units[u].height = std::max(units[u].height, units[succ].height + lag);
  return true;
}

//===----------------------------------------------------------------------===//
// Reads and writes of memory
//===----------------------------------------------------------------------===//

/// Whether the slice `mem` can issue a read on `cycle`: it issues nothing
/// else then, and no other result leaves it together with the word.
bool Scheduler::readFree(int mem, Cycle cycle, const Owner *mine) {
  auto free = [&](const Slots &slots, Cycle c) {
    const Owner *who = owner(slots, mem, c);
    return !who || (mine && who->kind == mine->kind &&
                    who->unit == mine->unit && who->operand == mine->operand);
  };
  if (walled && cycle < 0)
    return false;
  return free(st.issue, cycle) && free(st.exit, cycle + readDelay(mem));
}

void Scheduler::takeRead(int mem, Cycle cycle, int unit) {
  take(st.issue, mem, cycle, {Owner::Fixed, unit});
  take(st.exit, mem, cycle + readDelay(mem), {Owner::Fixed, unit});
}

bool Scheduler::holdsWrite(int p, int mem, Cycle cycle) const {
  const std::optional<Hold> &held = st.heldWrite[p];
  return held && held->mem == mem && held->cycle == cycle;
}

void Scheduler::releaseRead(int x, int k) {
  std::optional<Hold> &held = st.delivery[x][k].held;
  if (!held)
    return;
  drop(st.issue, held->mem, held->cycle);
  drop(st.exit, held->mem, held->cycle + readDelay(held->mem));
  set(held, std::optional<Hold>());
}

void Scheduler::releaseWrite(int p) {
  std::optional<Hold> &held = st.heldWrite[p];
  if (!held)
    return;
  drop(st.issue, held->mem, held->cycle);
  set(held, std::optional<Hold>());
}

/// Unit `x` has a cycle and the unit that makes its operand `k` has none:
/// hold a read on the nearest memory slice that has one free, in case the
/// word has to wait.
void Scheduler::holdRead(int x, int k) {
  const Operand &operand = units[x].operands[k];
  for (int mem : near[operand.slice]) {
    Cycle cycle = uses(x, k) - readLag(mem, operand.slice);
    if (!readFree(mem, cycle))
      continue;
    take(st.issue, mem, cycle, {Owner::Read, x, k});
    take(st.exit, mem, cycle + readDelay(mem), {Owner::Read, x, k});
    set(st.delivery[x][k].held, std::optional<Hold>(Hold{mem, cycle}));
    return;
  }
}

/// Unit `p` has a cycle and a user of its word has none: hold the write on
/// the nearest memory slice that is free when the word gets there.
bool Scheduler::holdWrite(int p) {
  for (int mem : near[instrs[units[p].result].slice]) {
    Cycle cycle = lands(p, mem);
    if (owner(st.issue, mem, cycle))
      continue;
    take(st.issue, mem, cycle, {Owner::Write, p});
    set(st.heldWrite[p], std::optional<Hold>(Hold{mem, cycle}));
    return true;
  }
  return fail(Why::NoMemory);
}

/// Whether a read or a write of these contents on `cycle` keeps the order
/// of the placed program: a read after the write that makes the contents
/// and before the next, a write after every read and the write before it.
bool Scheduler::inOrder(int version, Cycle cycle, bool write) {
  const Version &v = versions[version];
  auto time = [&](int other) -> std::optional<Cycle> {
    if (other < 0 || versions[other].store < 0)
      return std::nullopt;
    return st.time[versions[other].store];
  };
  if (!write) {
    std::optional<Cycle> made = time(version), next = time(v.next);
    if (made && cycle <= *made)
      return fail(Why::Order, v.slice, *made, versions[version].store);
    if (next && cycle >= *next)
      return fail(Why::Order, v.slice, *next, versions[v.next].store);
    return true;
  }
  std::optional<Cycle> before = time(v.prev), after = time(v.next);
  if (before && cycle <= *before)
    return fail(Why::Order, v.slice, *before, versions[v.prev].store);
  if (after && cycle >= *after)
    return fail(Why::Order, v.slice, *after, versions[v.next].store);
  if (v.prev >= 0)
    for (Cycle read : st.reads[v.prev])
      if (read >= cycle)
        return fail(Why::Order, v.slice, read);
  for (Cycle read : st.reads[version])
    if (read <= cycle)
      return fail(Why::Order, v.slice, read);
  return true;
}

//===----------------------------------------------------------------------===//
// Giving a word its way
//===----------------------------------------------------------------------===//

/// The cycle of the read that brings a word waiting in `mem` since `written`
/// to operand `k` of unit `x`, if the slice can issue it.
std::optional<Cycle> Scheduler::scratchRead(int x, int k, int mem,
                                            Cycle written) {
  Cycle cycle = uses(x, k) - readLag(mem, units[x].operands[k].slice);
  Owner mine{Owner::Read, x, k};
  if (cycle <= written || !readFree(mem, cycle, &mine))
    return std::nullopt;
  return cycle;
}

/// Bring a word that sits in the memory slice `from` to operand `k` of unit
/// `x` through a scratch word of a second memory slice: read it after cycle
/// `after`, write it there, and read it back on time. This is for an
/// instruction that needs two words of one memory slice on one cycle, which
/// that slice cannot issue together.
bool Scheduler::viaSecond(int x, int k, int from, Cycle after, int version) {
  const Operand &operand = units[x].operands[k];
  for (int mem : near[operand.slice]) {
    if (mem == from)
      continue;
    Cycle read = uses(x, k) - readLag(mem, operand.slice);
    if (!readFree(mem, read))
      continue;
    // The latest write that still leaves a cycle before the read.
    for (Cycle write = read - 1; write > read - 64; --write) {
      Cycle first = write - readLag(from, mem);
      if (first <= after || (walled && first < 0))
        break;
      if (owner(st.issue, mem, write) || !readFree(from, first))
        continue;
      Why kept = why;
      if (version >= 0 && !inOrder(version, first, false)) {
        why = kept;
        continue;
      }
      takeRead(from, first, x);
      take(st.issue, mem, write, {Owner::Fixed, x});
      takeRead(mem, read, x);
      if (version >= 0) {
        st.reads[version].push_back(first);
        undo.push_back([this, version] { st.reads[version].pop_back(); });
      }
      Delivery way = st.delivery[x][k];
      way.how = Delivery::Via;
      way.mem = mem;
      way.first = first;
      way.write = write;
      way.read = read;
      set(st.delivery[x][k], way);
      return true;
    }
  }
  return fail(Why::NoWay, operand.slice, uses(x, k));
}

/// Operand `k` of unit `x` is a word of a buffer: read it so that it
/// arrives on the cycle it is used.
bool Scheduler::readWord(int x, int k) {
  const Operand &operand = units[x].operands[k];
  const Version &version = versions[operand.version];
  Cycle cycle = uses(x, k) - readLag(version.slice, operand.slice);
  if (!readFree(version.slice, cycle)) {
    // Taken by another word for the same instruction: go round.
    const Owner *who = owner(st.issue, version.slice, cycle);
    if (who && who->kind == Owner::Fixed && who->unit == x)
      return viaSecond(x, k, version.slice, std::numeric_limits<Cycle>::min(),
                       operand.version);
    if (walled && cycle < 0)
      return fail(Why::TooEarly, version.slice, cycle);
    return fail(Why::Busy, version.slice, cycle, who ? who->unit : -1);
  }
  if (!inOrder(operand.version, cycle, false))
    return false;
  takeRead(version.slice, cycle, x);
  st.reads[operand.version].push_back(cycle);
  undo.push_back([this, v = operand.version] { st.reads[v].pop_back(); });
  Delivery way = st.delivery[x][k];
  way.how = Delivery::Load;
  way.read = cycle;
  set(st.delivery[x][k], way);
  return true;
}

/// Unit `p` has a cycle, and unit `x`, which uses its word as operand `k`,
/// has just been given one. The word goes directly if `x` is its one user
/// and it arrives exactly on time. Otherwise it waits in memory.
bool Scheduler::routeOne(int p, int x, int k) {
  const Operand &operand = units[x].operands[k];
  auto fromScratch = [&](Cycle read) {
    Hold where = *st.wait[p];
    releaseRead(x, k);
    takeRead(where.mem, read, x);
    Delivery way = st.delivery[x][k];
    way.how = Delivery::Scratch;
    way.read = read;
    set(st.delivery[x][k], way);
    return true;
  };

  if (st.wait[p]) {
    Hold where = *st.wait[p];
    if (std::optional<Cycle> read = scratchRead(x, k, where.mem, where.cycle))
      return fromScratch(*read);
    // Taken by another word for the same instruction: go round.
    Cycle read = uses(x, k) - readLag(where.mem, operand.slice);
    const Owner *who = owner(st.issue, where.mem, read);
    if (who && who->kind == Owner::Fixed && who->unit == x) {
      releaseRead(x, k);
      return viaSecond(x, k, where.mem, where.cycle, -1);
    }
    return fail(Why::NoWay, operand.slice, uses(x, k), p);
  }

  if (units[p].users.size() == 1 && uses(x, k) == lands(p, operand.slice)) {
    releaseWrite(p);
    releaseRead(x, k);
    Delivery way = st.delivery[x][k];
    way.how = Delivery::Direct;
    set(st.delivery[x][k], way);
    return true;
  }

  // The memory slices to try: the ones held for this word, then the nearest
  // to where it is made.
  std::vector<int> candidates;
  if (st.heldWrite[p])
    candidates.push_back(st.heldWrite[p]->mem);
  if (st.delivery[x][k].held)
    candidates.push_back(st.delivery[x][k].held->mem);
  for (int mem : near[instrs[units[p].result].slice])
    candidates.push_back(mem);
  std::set<int> tried;
  for (int mem : candidates) {
    if (!tried.insert(mem).second)
      continue;
    Cycle written = lands(p, mem);
    if (owner(st.issue, mem, written) && !holdsWrite(p, mem, written))
      continue;
    std::optional<Cycle> read = scratchRead(x, k, mem, written);
    if (!read)
      continue;
    releaseWrite(p);
    take(st.issue, mem, written, {Owner::Fixed, p});
    set(st.wait[p], std::optional<Hold>(Hold{mem, written}));
    return fromScratch(*read);
  }
  // Where the word can wait, its read is taken by another word for the same
  // instruction: let it wait there and go round.
  tried.clear();
  for (int mem : candidates) {
    if (!tried.insert(mem).second)
      continue;
    Cycle written = lands(p, mem);
    if (owner(st.issue, mem, written) && !holdsWrite(p, mem, written))
      continue;
    Cycle read = uses(x, k) - readLag(mem, operand.slice);
    const Owner *who = owner(st.issue, mem, read);
    if (read <= written || !who || who->kind != Owner::Fixed || who->unit != x)
      continue;
    size_t mark = undo.size();
    releaseWrite(p);
    releaseRead(x, k);
    take(st.issue, mem, written, {Owner::Fixed, p});
    set(st.wait[p], std::optional<Hold>(Hold{mem, written}));
    if (viaSecond(x, k, mem, written, -1))
      return true;
    rollback(mark);
  }
  return fail(Why::NoWay, operand.slice, uses(x, k), p);
}

/// Unit `p` has just been given a cycle, and `placed` are the users of its
/// word that have one already.
bool Scheduler::routeProducer(int p, const std::vector<User> &placed) {
  if (units[p].users.size() == 1) {
    User user = placed[0];
    if (uses(user.unit, user.operand) ==
        lands(p, units[user.unit].operands[user.operand].slice)) {
      releaseRead(user.unit, user.operand);
      Delivery way = st.delivery[user.unit][user.operand];
      way.how = Delivery::Direct;
      set(st.delivery[user.unit][user.operand], way);
      return true;
    }
  }

  std::vector<int> candidates;
  for (User user : placed)
    if (st.delivery[user.unit][user.operand].held)
      candidates.push_back(st.delivery[user.unit][user.operand].held->mem);
  for (int mem : near[instrs[units[p].result].slice])
    candidates.push_back(mem);
  std::set<int> tried;
  for (int mem : candidates) {
    if (!tried.insert(mem).second)
      continue;
    Cycle written = lands(p, mem);
    if (owner(st.issue, mem, written))
      continue;
    // One read for each user, on different cycles.
    std::vector<Cycle> reads;
    for (User user : placed) {
      std::optional<Cycle> read =
          scratchRead(user.unit, user.operand, mem, written);
      if (!read || llvm::is_contained(reads, *read))
        break;
      reads.push_back(*read);
    }
    if (reads.size() != placed.size())
      continue;
    take(st.issue, mem, written, {Owner::Fixed, p});
    set(st.wait[p], std::optional<Hold>(Hold{mem, written}));
    for (size_t i = 0; i < placed.size(); ++i) {
      User user = placed[i];
      releaseRead(user.unit, user.operand);
      takeRead(mem, reads[i], user.unit);
      Delivery way = st.delivery[user.unit][user.operand];
      way.how = Delivery::Scratch;
      way.read = reads[i];
      set(st.delivery[user.unit][user.operand], way);
    }
    return true;
  }
  // No memory slice is free for every read. The users' cycles are fixed, so
  // no other cycle for this unit changes that: let the word wait where it
  // can, and bring it round through a second memory slice to each user
  // whose read is taken.
  tried.clear();
  for (int mem : candidates) {
    if (!tried.insert(mem).second)
      continue;
    Cycle written = lands(p, mem);
    if (owner(st.issue, mem, written))
      continue;
    size_t mark = undo.size();
    take(st.issue, mem, written, {Owner::Fixed, p});
    set(st.wait[p], std::optional<Hold>(Hold{mem, written}));
    bool found = true;
    for (User user : placed) {
      std::optional<Cycle> read =
          scratchRead(user.unit, user.operand, mem, written);
      releaseRead(user.unit, user.operand);
      if (read) {
        takeRead(mem, *read, user.unit);
        Delivery way = st.delivery[user.unit][user.operand];
        way.how = Delivery::Scratch;
        way.read = *read;
        set(st.delivery[user.unit][user.operand], way);
      } else if (!viaSecond(user.unit, user.operand, mem, written, -1)) {
        found = false;
        break;
      }
    }
    if (found)
      return true;
    rollback(mark);
  }
  User user = placed[0];
  return fail(Why::NoWay, units[user.unit].operands[user.operand].slice,
              uses(user.unit, user.operand), user.unit);
}

//===----------------------------------------------------------------------===//
// Giving a unit a cycle
//===----------------------------------------------------------------------===//

/// Give unit `u` the cycle `time`: take its slots, and give every word both
/// of whose ends now have a cycle its way. On failure the schedule is left
/// half changed; `tryPlace` takes the changes back.
bool Scheduler::place(int u, Cycle time) {
  const Unit &unit = units[u];

  // A slot held for a word gives way to the instruction the word was held
  // for: the one user that will take the word directly, and the store that
  // is the write.
  if (unit.result >= 0 && unit.users.size() == 1) {
    User user = unit.users[0];
    if (st.time[user.unit] &&
        uses(user.unit, user.operand) ==
            lands(u, time, units[user.unit].operands[user.operand].slice))
      releaseRead(user.unit, user.operand);
  }
  if (unit.isStore && unit.stores >= 0 && st.time[unit.stores] &&
      holdsWrite(unit.stores, instrs[unit.instrs[0]].slice, time))
    releaseWrite(unit.stores);

  // Its own slots: one instruction at a slice on a cycle (Machine 3.3), and
  // one result leaving a slice on a cycle (Machine 3.4).
  for (int i : unit.instrs) {
    const Instr &in = instrs[i];
    Cycle cycle = time + in.offset;
    if (walled && cycle < 0)
      return fail(Why::TooEarly, in.slice, cycle);
    if (const Owner *who = owner(st.issue, in.slice, cycle))
      return fail(Why::Busy, in.slice, cycle, who->unit);
    take(st.issue, in.slice, cycle, {Owner::Fixed, u});
    if (!in.hasResult)
      continue;
    if (const Owner *who = owner(st.exit, in.slice, cycle + in.delay))
      return fail(Why::Leaving, in.slice, cycle + in.delay, who->unit);
    take(st.exit, in.slice, cycle + in.delay, {Owner::Fixed, u});
  }
  set(st.time[u], std::optional<Cycle>(time));

  // Every dependence on a unit that has a cycle already.
  const Instr &head = instrs[unit.instrs[0]];
  for (auto [pred, lag] : unit.preds)
    if (st.time[pred] && time < *st.time[pred] + lag)
      return fail(Why::Order, head.slice, *st.time[pred], pred);
  for (auto [succ, lag] : unit.succs)
    if (st.time[succ] && *st.time[succ] < time + lag)
      return fail(Why::Order, head.slice, *st.time[succ], succ);

  // A write to a buffer, or a read that is a unit, in the order of the
  // placed program.
  if (head.version >= 0) {
    if (!inOrder(head.version, time, unit.isStore))
      return false;
    if (!unit.isStore) {
      st.reads[head.version].push_back(time);
      undo.push_back([this, v = head.version] { st.reads[v].pop_back(); });
    }
  }

  // The words it uses. Buffer words first, then words whose makers have a
  // cycle, and last the slots held for words whose makers have none, so that
  // a held slot never takes one this unit's own reads need.
  int operands = static_cast<int>(unit.operands.size());
  for (int k = 0; k < operands; ++k)
    if (unit.operands[k].version >= 0 && !readWord(u, k))
      return false;
  for (int k = 0; k < operands; ++k) {
    int producer = unit.operands[k].producer;
    if (producer >= 0 && st.time[producer] && !routeOne(producer, u, k))
      return false;
  }
  for (int k = 0; k < operands; ++k) {
    int producer = unit.operands[k].producer;
    if (producer >= 0 && !st.time[producer])
      holdRead(u, k);
  }

  // The word it makes.
  if (unit.result >= 0) {
    std::vector<User> placed;
    for (User user : unit.users)
      if (st.time[user.unit])
        placed.push_back(user);
    if (!placed.empty() && !routeProducer(u, placed))
      return false;
    if (!st.wait[u] && placed.size() < unit.users.size() && !holdWrite(u))
      return false;
  }
  set(st.placed, st.placed + 1);
  return true;
}

bool Scheduler::tryPlace(int u, Cycle time) {
  size_t mark = undo.size();
  if (place(u, time))
    return true;
  rollback(mark);
  return false;
}

/// Backward: give unit `u` the cycle `time`, and each store of its word the
/// first cycle it fits from when the word gets there.
bool Scheduler::tryWithStores(int u, Cycle time) {
  size_t mark = undo.size();
  if (!place(u, time)) {
    rollback(mark);
    return false;
  }
  for (User user : units[u].users) {
    const Unit &store = units[user.unit];
    if (!store.together || store.stores != u || store.pin ||
        st.time[user.unit])
      continue;
    Cycle from = lands(u, instrs[store.instrs[0]].slice);
    bool done = false;
    for (Cycle cycle = from; cycle < from + 64 && !done; ++cycle)
      done = tryPlace(user.unit, cycle);
    if (!done) {
      rollback(mark);
      return false;
    }
  }
  return true;
}

//===----------------------------------------------------------------------===//
// The walks
//===----------------------------------------------------------------------===//

/// Forward: whether a word that unit `u` uses arrives exactly on the cycle
/// `u` would use it, if `u` were given `time`.
bool Scheduler::arrivesNow(int u, Cycle time) const {
  for (const Operand &operand : units[u].operands) {
    int p = operand.producer;
    if (p >= 0 && st.time[p] && !st.wait[p] && units[p].users.size() == 1 &&
        lands(p, operand.slice) == time + operand.offset)
      return true;
  }
  return false;
}

/// Backward: whether the word of unit `u`, if `u` were given `time`,
/// arrives exactly on the cycle its one user uses it.
bool Scheduler::wantedNow(int u, Cycle time) const {
  const Unit &unit = units[u];
  if (unit.result < 0 || unit.users.size() != 1)
    return false;
  User user = unit.users[0];
  return st.time[user.unit] &&
         lands(u, time, units[user.unit].operands[user.operand].slice) ==
             uses(user.unit, user.operand);
}

/// Backward: whether the store `s` goes with the unit that makes its word,
/// which is one of the `chosen`.
bool Scheduler::storeGoesWith(int s, const std::vector<bool> &chosen) const {
  const Unit &store = units[s];
  return store.together && !store.pin && chosen[store.stores];
}

/// For each unit without a cycle, the latest cycle it can have: every unit
/// that waits for it and has a cycle is far enough after it, directly or
/// through units that have none yet. `never` if nothing bounds it.
std::vector<Cycle> Scheduler::latest() const {
  std::vector<Cycle> bound(units.size(), never);
  for (size_t u = units.size(); u-- > 0;)
    for (auto [succ, lag] : units[u].succs) {
      Cycle at = st.time[succ] ? *st.time[succ] : bound[succ];
      if (at != never)
        bound[u] = std::min(bound[u], at - lag);
    }
  return bound;
}

/// A pinned unit that waits for unit `u`, directly or not, for an error
/// message.
int Scheduler::pinAfter(int u) const {
  std::vector<int> todo{u};
  std::set<int> seen;
  while (!todo.empty()) {
    int next = todo.back();
    todo.pop_back();
    if (!seen.insert(next).second)
      continue;
    if (units[next].pin)
      return next;
    for (auto [succ, lag] : units[next].succs)
      todo.push_back(succ);
  }
  return -1;
}

/// Refuse a program because unit `u` cannot come before a pinned unit that
/// waits for it.
bool Scheduler::tooLate(int u, StringRef what) {
  int pinned = pinAfter(u);
  if (pinned < 0)
    return refuse(instrs[units[u].instrs[0]].op, what);
  return refuse(instrs[units[u].instrs[0]].op, what, units[pinned].pinned,
                "pinned to cycle " +
                    Twine(tau::intAttr(*units[pinned].pinned, "pin")) + " here");
}

/// Walk the cycles upward from `from`, giving each ready unit the first
/// cycle it fits. A unit is ready when every unit it waits for has a cycle.
bool Scheduler::forward(Cycle from) {
  for (Cycle now = from; st.placed < units.size(); ++now) {
    std::vector<Cycle> bound = latest();
    std::vector<int> ready;
    for (size_t u = 0; u < units.size(); ++u) {
      if (st.time[u])
        continue;
      bool waits = false;
      for (auto [pred, lag] : units[u].preds)
        waits |= !st.time[pred];
      if (waits)
        continue;
      // What already has a cycle may need this unit earlier than now.
      if (bound[u] < now)
        return tooLate(static_cast<int>(u),
                       "cannot be issued in time for an instruction that is "
                       "pinned");
      ready.push_back(static_cast<int>(u));
    }
    // A word that arrives exactly now; then the unit with the least time
    // left, if a pin leaves it a last cycle; then the longest path to the
    // end; then program order.
    std::vector<char> exact(units.size());
    for (int u : ready)
      exact[u] = arrivesNow(u, now);
    std::stable_sort(ready.begin(), ready.end(), [&](int a, int b) -> bool {
      if (exact[a] != exact[b])
        return exact[a];
      if (bound[a] != bound[b])
        return bound[a] < bound[b];
      return units[a].height > units[b].height;
    });
    for (int u : ready)
      if (!tryPlace(u, now) && now > st.high + beyond())
        return stuck(u);
  }
  return true;
}

/// Walk the cycles downward from `from`, giving each of the `chosen` units
/// that is ready the first cycle it fits. A unit is ready when every unit
/// that waits for it, directly or not, and is to be given a cycle by this
/// walk, has one. With `wall`, nothing may be issued before cycle 0.
bool Scheduler::backward(const std::vector<bool> &chosen, Cycle from,
                         bool wall) {
  for (Cycle now = from;; --now) {
    std::vector<Cycle> bound = latest();
    // For each unit, the units this walk has still to place that wait for
    // it, directly or not: none (-1), one, or several (-2). A store that
    // goes with the unit that makes its word counts as that unit, and a unit
    // does not wait for itself.
    const int none = -1, several = -2;
    std::vector<int> waiting(units.size(), none);
    auto add = [&](int &to, int who) {
      if (who != none)
        to = to == none || to == who ? who : several;
    };
    for (size_t u = units.size(); u-- > 0;)
      for (auto [succ, lag] : units[u].succs) {
        if (st.time[succ])
          continue;
        if (storeGoesWith(succ, chosen))
          add(waiting[u], units[succ].stores);
        else if (chosen[succ])
          add(waiting[u], succ);
        add(waiting[u], waiting[succ]);
      }
    std::vector<int> ready;
    int left = -1;
    for (size_t u = 0; u < units.size(); ++u) {
      if (!chosen[u] || st.time[u] ||
          storeGoesWith(static_cast<int>(u), chosen))
        continue;
      left = static_cast<int>(u);
      if ((waiting[u] == none || waiting[u] == left) && now <= bound[u])
        ready.push_back(left);
    }
    if (left < 0)
      return true;
    if (wall && now < 0)
      return tooLate(left, "cannot be issued early enough for an instruction "
                           "that is pinned");
    // Nothing is ready, and nothing becomes ready by walking on: the units
    // that are left wait for each other.
    if (ready.empty() && now < st.low - beyond())
      return stuck(left);
    // A word that, issued now, arrives exactly when it is used; then the
    // longest path from the start; then program order.
    std::vector<char> exact(units.size());
    for (int u : ready)
      exact[u] = wantedNow(u, now);
    std::stable_sort(ready.begin(), ready.end(), [&](int a, int b) -> bool {
      if (exact[a] != exact[b])
        return exact[a];
      return units[a].depth > units[b].depth;
    });
    for (int u : ready)
      if (!tryWithStores(u, now) && now < st.low - beyond())
        return stuck(u);
  }
}

/// A program with pins. Each pinned unit gets its cycle. Then the units
/// whose words have to reach a pinned unit are walked backward from the
/// pins, so that each word arrives exactly if it can; and a forward walk
/// takes the rest.
bool Scheduler::pins() {
  walled = true;
  Cycle top = 0;
  for (size_t u = 0; u < units.size(); ++u) {
    const Unit &unit = units[u];
    if (!unit.pin)
      continue;
    Cycle pin = tau::intAttr(*unit.pinned, "pin");
    if (!tryPlace(static_cast<int>(u), *unit.pin)) {
      bool other = why.other >= 0 && why.other != static_cast<int>(u);
      return refuse(unit.pinned,
                    "pinned to cycle " + Twine(pin) + ", but " + describe(why),
                    other ? instrs[units[why.other].instrs[0]].op : nullptr,
                    "the other instruction is here");
    }
    top = std::max(top, *unit.pin + unit.length);
  }

  // The units to walk backward. First everything a pinned unit takes a word
  // from, and so on back: these are a fixed number of cycles before the pin
  // if their words are to go directly.
  std::vector<bool> before(units.size());
  for (size_t u = units.size(); u-- > 0;)
    if (units[u].pin || before[u])
      for (const Operand &operand : units[u].operands)
        if (operand.producer >= 0 && !units[operand.producer].pin)
          before[operand.producer] = true;
  // Then everything between one of those and a pinned unit: it waits for a
  // unit the walk places, and a pinned unit waits for it. Left to the
  // forward walk it would come after a unit that was placed as late as the
  // pin allows, with no room to spare.
  std::vector<bool> pinWaits(units.size()), after(units.size());
  for (size_t u = units.size(); u-- > 0;)
    for (auto [succ, lag] : units[u].succs)
      if (units[succ].pin || pinWaits[succ])
        pinWaits[u] = true;
  for (size_t u = 0; u < units.size(); ++u)
    for (auto [pred, lag] : units[u].preds)
      if (before[pred] || after[pred])
        after[u] = true;
  for (size_t u = 0; u < units.size(); ++u)
    if (after[u] && pinWaits[u] && !units[u].pin)
      before[u] = true;

  return backward(before, top, true) && forward(0);
}

void Scheduler::reset() {
  st = Schedule();
  st.time.assign(units.size(), std::nullopt);
  st.wait.assign(units.size(), std::nullopt);
  st.heldWrite.assign(units.size(), std::nullopt);
  st.delivery.resize(units.size());
  for (size_t u = 0; u < units.size(); ++u)
    st.delivery[u].assign(units[u].operands.size(), Delivery());
  st.reads.assign(versions.size(), {});
  undo.clear();
  refusal = Refusal();
}

/// The first and the last cycle on which a schedule issues anything.
Cycle Scheduler::first(const Schedule &s) const {
  Cycle least = std::numeric_limits<Cycle>::max();
  for (const auto &slot : s.issue)
    least = std::min(least, slot.first.second);
  return s.issue.empty() ? 0 : least;
}

Cycle Scheduler::last(const Schedule &s) const {
  Cycle most = std::numeric_limits<Cycle>::min();
  for (const auto &slot : s.issue)
    most = std::max(most, slot.first.second);
  return s.issue.empty() ? 0 : most;
}

/// The number of words a schedule sends through memory.
size_t Scheduler::waits(const Schedule &s) const {
  size_t count = 0;
  for (const std::optional<Hold> &wait : s.wait)
    count += wait.has_value();
  for (const auto &ways : s.delivery)
    for (const Delivery &way : ways)
      count += way.how == Delivery::Via;
  return count;
}

std::string Scheduler::describe(const Why &w) const {
  std::string text;
  raw_string_ostream out(text);
  switch (w.kind) {
  case Why::Busy:
    out << "slice " << w.slice << " would have two instructions on cycle "
        << w.cycle;
    break;
  case Why::Leaving:
    out << "two results would leave slice " << w.slice << " on cycle "
        << w.cycle;
    break;
  case Why::TooEarly:
    out << "slice " << w.slice
        << " would have to issue an instruction for it before cycle 0";
    break;
  case Why::Order:
    out << "it would be on the wrong side of the instruction on cycle "
        << w.cycle << " that the program puts before or after it";
    break;
  case Why::NoWay:
    out << "a word it uses cannot be at slice " << w.slice << " on cycle "
        << w.cycle << ", neither directly nor through memory";
    break;
  case Why::NoMemory:
    out << "no memory slice is free to keep its word when it gets there";
    break;
  case Why::Nothing:
    out << "nothing fits";
    break;
  }
  return text;
}

bool Scheduler::refuse(Operation *op, const Twine &message, Operation *noted,
                       const Twine &note) {
  refusal = {op, message.str(), noted, note.str()};
  return false;
}

/// Refuse a program because a walk finds no cycle for unit `u`.
bool Scheduler::stuck(int u) {
  return refuse(instrs[units[u].instrs[0]].op,
                "no cycle was found for this instruction: " + describe(why));
}

void Scheduler::report() {
  InFlightDiagnostic diag = refusal.op->emitError(refusal.message);
  if (refusal.noted)
    diag.attachNote(refusal.noted->getLoc()) << refusal.note;
}

bool Scheduler::run() {
  if (!build())
    return false;

  reset();
  if (hasPins) {
    if (!pins()) {
      report();
      return false;
    }
  } else {
    // Both directions, each a single walk. Keep the shorter; on a tie the
    // one with fewer words through memory, and then the forward one.
    bool found = forward(0);
    Schedule ahead = st;
    Refusal why = refusal;
    reset();
    std::vector<bool> chosen(units.size());
    for (size_t u = 0; u < units.size(); ++u)
      chosen[u] = !units[u].together;
    bool back = backward(chosen, 0, false);
    if (!back) {
      if (!found) {
        refusal = why;
        report();
        return false;
      }
      st = ahead;
    } else if (found) {
      Cycle forwardLength = last(ahead) - first(ahead);
      Cycle backwardLength = last(st) - first(st);
      if (forwardLength < backwardLength ||
          (forwardLength == backwardLength && waits(ahead) <= waits(st)))
        st = ahead;
    }
    undo.clear();
  }
  write();
  return true;
}

//===----------------------------------------------------------------------===//
// Writing the schedule into the function
//===----------------------------------------------------------------------===//

void Scheduler::write() {
  Block &block = func.getBody().front();
  OpBuilder builder(func.getContext());
  builder.setInsertionPoint(block.getTerminator());
  Type wordType = tau::WordType::get(func.getContext());
  Cycle start = walled ? 0 : first(st);

  std::vector<std::pair<Cycle, Operation *>> timed;
  auto issue = [&](Operation *op, Cycle cycle) {
    tau::setIntAttr(*op, "time", cycle - start);
    timed.push_back({cycle - start, op});
  };
  auto read = [&](Location loc, int slice, int64_t addr, Cycle cycle) {
    OperationState state(loc, "tau.i.read");
    state.addTypes({wordType});
    state.addAttribute("slice", builder.getI64IntegerAttr(slice));
    state.addAttribute("addr", builder.getI64IntegerAttr(addr));
    Operation *op = builder.create(state);
    issue(op, cycle);
    return op->getResult(0);
  };
  auto writeWord = [&](Location loc, Value word, int slice, int64_t addr,
                       Cycle cycle) {
    OperationState state(loc, "tau.i.write");
    state.addOperands({word});
    state.addAttribute("slice", builder.getI64IntegerAttr(slice));
    state.addAttribute("addr", builder.getI64IntegerAttr(addr));
    issue(builder.create(state), cycle);
  };

  // Scratch words: one for each word that waits, numbered in each memory
  // slice in the order they are written, after the buffers.
  std::vector<int64_t> sizes;
  for (Attribute size : func->getAttrOfType<ArrayAttr>("tau.mem_sizes"))
    sizes.push_back(cast<IntegerAttr>(size).getInt());
  struct Scratch {
    int mem;
    Cycle written;
    int64_t *addr;
  };
  std::vector<Scratch> scratch;
  std::vector<int64_t> waitAddr(units.size(), 0);
  std::vector<std::vector<int64_t>> viaAddr(units.size());
  for (size_t u = 0; u < units.size(); ++u) {
    if (st.wait[u])
      scratch.push_back({st.wait[u]->mem, st.wait[u]->cycle, &waitAddr[u]});
    viaAddr[u].assign(units[u].operands.size(), 0);
    for (size_t k = 0; k < units[u].operands.size(); ++k)
      if (st.delivery[u][k].how == Delivery::Via)
        scratch.push_back({st.delivery[u][k].mem, st.delivery[u][k].write,
                           &viaAddr[u][k]});
  }
  std::stable_sort(scratch.begin(), scratch.end(),
                   [](const Scratch &a, const Scratch &b) {
                     return a.written < b.written;
                   });
  for (const Scratch &word : scratch)
    *word.addr = sizes[word.mem]++;

  for (size_t u = 0; u < units.size(); ++u) {
    const Unit &unit = units[u];
    for (int i : unit.instrs)
      issue(instrs[i].op, *st.time[u] + instrs[i].offset);
    if (st.wait[u])
      writeWord(instrs[unit.result].op->getLoc(),
                instrs[unit.result].op->getResult(0), st.wait[u]->mem,
                waitAddr[u], st.wait[u]->cycle);
  }
  for (size_t u = 0; u < units.size(); ++u)
    for (size_t k = 0; k < units[u].operands.size(); ++k) {
      const Operand &operand = units[u].operands[k];
      const Delivery &way = st.delivery[u][k];
      Location loc = operand.uses[0]->getOwner()->getLoc();
      Value word;
      // Where the word is before it is brought here: its buffer word, or
      // the scratch word it waits in.
      int from = 0;
      int64_t addr = 0;
      if (operand.version >= 0) {
        from = versions[operand.version].slice;
        addr = versions[operand.version].addr;
      } else if (st.wait[operand.producer]) {
        from = st.wait[operand.producer]->mem;
        addr = waitAddr[operand.producer];
      }
      switch (way.how) {
      case Delivery::None:
      case Delivery::Direct:
        continue;
      case Delivery::Scratch:
      case Delivery::Load:
        word = read(loc, from, addr, way.read);
        break;
      case Delivery::Via:
        writeWord(loc, read(loc, from, addr, way.first), way.mem,
                  viaAddr[u][k], way.write);
        word = read(loc, way.mem, viaAddr[u][k], way.read);
        break;
      }
      for (OpOperand *use : operand.uses)
        use->set(word);
    }
  for (Operation *op : perUser)
    op->erase();

  // In order of time, which puts every word before its users.
  std::stable_sort(timed.begin(), timed.end(),
                   [](const auto &a, const auto &b) { return a.first < b.first; });
  Cycle cycles = 0;
  for (auto &[cycle, op] : timed) {
    op->moveBefore(block.getTerminator());
    cycles = std::max(cycles, cycle + 1);
    // A result nobody reads is still inside its slice; let it leave.
    Value result = tau::streamResult(*op);
    if (result && result.use_empty())
      cycles = std::max(cycles, cycle + machine.maxDelay() + 2);
  }

  // A stream of its own for every word, on a machine with enough streams.
  int64_t fresh[2] = {0, 0};
  for (auto &[cycle, op] : timed) {
    Value result = tau::streamResult(*op);
    if (!result)
      continue;
    bool east = tau::goesEast(*op).value_or(true);
    op->setAttr("east", builder.getBoolAttr(east));
    tau::setIntAttr(*op, "stream", fresh[east]++);
  }
  func->setAttr("tau.streams", builder.getI64IntegerAttr(machine.streams));
  tau::Machine widened = machine;
  widened.streams = static_cast<int>(
      std::max<int64_t>(machine.streams, std::max(fresh[0], fresh[1])));
  tau::setMachine(func, widened);
  func->setAttr("tau.mem_sizes", builder.getI64ArrayAttr(sizes));
  func->setAttr("tau.cycles", builder.getI64IntegerAttr(cycles));
}

struct SchedulePass : PassWrapper<SchedulePass, OperationPass<func::FuncOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(SchedulePass)

  StringRef getArgument() const final { return "tau-schedule"; }
  StringRef getDescription() const final {
    return "Give every instruction a cycle";
  }

  void runOnOperation() override {
    func::FuncOp func = getOperation();
    Expected<tau::Machine> machine = tau::machineOf(func);
    if (!machine) {
      func.emitError(toString(machine.takeError()));
      return signalPassFailure();
    }
    Scheduler scheduler(func, *machine);
    if (!scheduler.run())
      signalPassFailure();
  }
};

} // namespace

std::unique_ptr<Pass> tau::createSchedulePass() {
  return std::make_unique<SchedulePass>();
}
