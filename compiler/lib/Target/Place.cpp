//===- Place.cpp - the tau-place pass -------------------------------------===//
//
// Turns a kernel with no loops into instructions.
//
// Placement of buffers. Buffers are spread over the memory slices in turn.
// Words of memory beyond the buffers are scratch space.
//
// Placement of operations. An operation runs on a slice of the kind it
// needs. Where the chip has several, it takes the one nearest to where its
// operand comes from.
//
// Stored matrices. A matrix slice can keep the columns of a matrix. When the
// same matrix is multiplied again later, with no store to its buffer in
// between, the pass installs the columns once and every product then uses
// the stored columns instead of streaming them from memory again.
//
// Grouping. A word can only wait in memory, so the pass has to decide which
// values travel straight from the operation that makes them to the operation
// that uses them, and which are written to memory and read back. It builds
// *groups*. A group is a chain of operations in which each result is used
// only by the next operation. Every other operand of a chained operation is
// read from memory. The last result is written to memory, or straight to the
// buffer if the kernel stores it there.
//
// A chain is only extended while the following holds, which lets
// `tau-schedule` give every group a schedule with no two instructions on one
// slice in one cycle:
//
//   * no memory slice is read for two different operations of the group, and
//   * operands that must arrive together (the two of a two-word operation,
//     the three of a select) are not read from the same slice.
//
// When the second condition fails for a single operation, operands are first
// copied to scratch words in other slices.
//
// The pass records the chip, the memory map and the memory sizes on the
// function. It does not choose cycles or streams.
//
// Nothing here is proved. `tau-check kernel.json placed.json` decides whether
// the instructions, run in order, compute what the kernel computes.
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Target/Target.h"
#include "tau/Transforms/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/Pass/Pass.h"
#include "llvm/ADT/DenseMap.h"

#include <map>
#include <optional>
#include <set>

using namespace llvm;
using namespace mlir;

namespace {

/// A word of memory.
struct Loc {
  int slice = -1;
  int64_t addr = 0;

  bool operator==(const Loc &other) const {
    return slice == other.slice && addr == other.addr;
  }
  bool operator<(const Loc &other) const {
    return std::tie(slice, addr) < std::tie(other.slice, other.addr);
  }
};

/// The columns of a matrix: `n` words of a buffer starting at `base`.
struct Matrix {
  int buf;
  int64_t base;
  int64_t n;

  bool operator==(const Matrix &other) const {
    return buf == other.buf && base == other.base && n == other.n;
  }
};

/// One operation of the kernel, with values and buffers as numbers.
struct Node {
  enum Kind { Load, Store, Un, Bin, MatVec, Const, Sel } kind;
  std::string fn;
  std::optional<int64_t> k;
  std::vector<int64_t> table;
  std::vector<int64_t> values;
  int dst = -1;
  /// The values used: one for `Un` and `Store`, two for `Bin`, three for
  /// `Sel` (mask first), and the vector then the optional bias for `MatVec`.
  std::vector<int> args;
  int buf = -1;
  int64_t base = 0;
  int64_t n = 0;
};

/// How a matrix-vector product gets its columns.
struct MatMode {
  int slice = -1;
  /// Use columns stored in the slice, not streamed from memory.
  bool stored = false;
  /// The columns have to be installed first.
  bool install = false;
};

class Placer {
public:
  Placer(func::FuncOp func, const tau::Chip &chip)
      : func(func), chip(chip), builder(func.getContext()) {}

  Error run();

private:
  func::FuncOp func;
  const tau::Chip &chip;
  OpBuilder builder;
  Type word;
  Type acc;

  std::vector<Node> nodes;
  std::vector<int64_t> bufSizes;
  /// For each value, the operations that use it.
  std::vector<std::vector<int>> uses;
  /// A load whose word can be read where its value is used, because no store
  /// to its buffer comes in between.
  std::vector<bool> isVirtual;

  std::vector<int> mems;
  std::vector<int> sxms;
  std::vector<int> mxms;
  int vxm = -1;
  /// Words of memory handed out so far at each position.
  std::vector<int64_t> used;
  std::vector<Loc> bufLoc;
  size_t nextScratch = 0;

  /// Where each value can be read from memory, once it can.
  std::vector<std::optional<Loc>> valueLoc;
  std::vector<bool> done;
  /// The matrix whose columns each matrix slice currently stores.
  std::map<int, Matrix> installed;

  Error read();
  static int nearest(const std::vector<int> &candidates, int from);
  int sliceOf(const Node &node, int from) const;
  int origin(const Node &node) const;
  Loc newScratch(const std::set<int> &avoid);
  int chainNext(int index) const;
  bool usedAgain(int index) const;
  MatMode decide(int index, int from) const;
  bool admit(const Node &node, int flight, const MatMode &mode,
             std::set<int> &readSlices) const;
  void forget(int buf);
  Error placeComputed(int index);

  // Building instructions.
  Operation *make(StringRef name, ArrayRef<Value> operands,
                  ArrayRef<Type> results, ArrayRef<NamedAttribute> attrs);
  NamedAttribute attr(StringRef name, int64_t value) {
    return builder.getNamedAttr(name, builder.getI64IntegerAttr(value));
  }
  Value emitRead(Loc loc);
  void emitWrite(Value value, Loc loc);
  void emitCopy(Loc from, Loc to) { emitWrite(emitRead(from), to); }
};

Error Placer::read() {
  llvm::DenseMap<Value, int> buffers;
  llvm::DenseMap<Value, int> values;
  for (BlockArgument arg : func.getArguments()) {
    auto buf = dyn_cast<tau::BufType>(arg.getType());
    if (!buf)
      return createStringError("every argument must be a !tau.buf");
    buffers[arg] = static_cast<int>(bufSizes.size());
    bufSizes.push_back(buf.getSize());
  }
  auto define = [&](Value value) {
    int id = static_cast<int>(values.size());
    values[value] = id;
    return id;
  };

  for (Operation &op : func.getBody().front()) {
    if (isa<func::ReturnOp>(op))
      continue;
    Node node;
    if (auto load = dyn_cast<tau::LoadOp>(op)) {
      node.kind = Node::Load;
      node.buf = buffers.lookup(load.getBuf());
      node.base = load.getBase();
      node.dst = define(load.getResult());
    } else if (auto store = dyn_cast<tau::StoreOp>(op)) {
      node.kind = Node::Store;
      node.args = {values.lookup(store.getValue())};
      node.buf = buffers.lookup(store.getBuf());
      node.base = store.getBase();
    } else if (auto matvec = dyn_cast<tau::MatVecOp>(op)) {
      node.kind = Node::MatVec;
      node.args = {values.lookup(matvec.getX())};
      node.buf = buffers.lookup(matvec.getBuf());
      node.base = matvec.getBase();
      node.n = matvec.getN();
      node.dst = define(matvec.getResult());
    } else if (auto affine = dyn_cast<tau::AffineOp>(op)) {
      node.kind = Node::MatVec;
      node.args = {values.lookup(affine.getX()),
                   values.lookup(affine.getBias())};
      node.buf = buffers.lookup(affine.getBuf());
      node.base = affine.getBase();
      node.n = affine.getN();
      node.dst = define(affine.getResult());
    } else if (auto constant = dyn_cast<tau::ConstOp>(op)) {
      node.kind = Node::Const;
      node.values = constant.getValues();
      node.dst = define(constant.getResult());
    } else if (auto select = dyn_cast<tau::SelectOp>(op)) {
      node.kind = Node::Sel;
      node.args = {values.lookup(select.getM()), values.lookup(select.getA()),
                   values.lookup(select.getB())};
      node.dst = define(select.getResult());
    } else if (tau::isBinaryKernelOp(op)) {
      node.kind = Node::Bin;
      node.fn = tau::kernelName(op).str();
      node.args = {values.lookup(op.getOperand(0)),
                   values.lookup(op.getOperand(1))};
      node.dst = define(op.getResult(0));
    } else if (tau::isUnaryKernelOp(op)) {
      node.kind = Node::Un;
      node.fn = tau::kernelName(op).str();
      if (auto k = op.getAttrOfType<IntegerAttr>("k"))
        node.k = k.getInt();
      if (auto table = op.getAttrOfType<DenseI64ArrayAttr>("table"))
        node.table = table.asArrayRef();
      node.args = {values.lookup(op.getOperand(0))};
      node.dst = define(op.getResult(0));
    } else if (isa<tau::ForOp>(op)) {
      return createStringError("run tau-unroll before tau-place");
    } else {
      return createStringError("cannot place operation '" +
                               op.getName().getStringRef() + "'");
    }
    nodes.push_back(std::move(node));
  }

  uses.assign(values.size(), {});
  for (int i = 0, e = static_cast<int>(nodes.size()); i < e; ++i)
    for (int arg : nodes[i].args)
      uses[arg].push_back(i);

  // A load is virtual if no store to its buffer lies between it and any use.
  isVirtual.assign(nodes.size(), false);
  for (int i = 0, e = static_cast<int>(nodes.size()); i < e; ++i) {
    if (nodes[i].kind != Node::Load)
      continue;
    bool safe = true;
    for (int use : uses[nodes[i].dst])
      for (int j = i + 1; j < use; ++j)
        if (nodes[j].kind == Node::Store && nodes[j].buf == nodes[i].buf)
          safe = false;
    isVirtual[i] = safe;
  }

  valueLoc.assign(values.size(), std::nullopt);
  done.assign(nodes.size(), false);
  return Error::success();
}

int Placer::nearest(const std::vector<int> &candidates, int from) {
  int best = -1;
  for (int candidate : candidates)
    if (best < 0 || std::abs(candidate - from) < std::abs(best - from))
      best = candidate;
  return best;
}

/// The slice an operation runs on, given where its operand comes from.
/// Matrix-vector products are placed by `decide`.
int Placer::sliceOf(const Node &node, int from) const {
  if (node.kind == Node::Un && tau::isRearrangement(node.fn))
    return nearest(sxms, from);
  return vxm;
}

/// Where the first operand of an operation that starts a group comes from.
int Placer::origin(const Node &node) const {
  for (int arg : node.args)
    if (valueLoc[arg])
      return valueLoc[arg]->slice;
  return vxm;
}

Loc Placer::newScratch(const std::set<int> &avoid) {
  for (size_t tries = 0; tries < mems.size(); ++tries) {
    int slice = mems[(nextScratch + tries) % mems.size()];
    if (avoid.count(slice))
      continue;
    nextScratch += tries + 1;
    return {slice, used[slice]++};
  }
  return {};
}

/// If the result of operation `index` has exactly one use, and only virtual
/// loads lie between the two, return the using operation. Otherwise -1.
int Placer::chainNext(int index) const {
  int value = nodes[index].dst;
  if (value < 0 || uses[value].size() != 1)
    return -1;
  int use = uses[value][0];
  for (int j = index + 1; j < use; ++j)
    if (!(nodes[j].kind == Node::Load && isVirtual[j]))
      return -1;
  return use;
}

/// Whether the matrix of the product at `index` is multiplied again later,
/// before anything is stored to its buffer.
bool Placer::usedAgain(int index) const {
  const Node &node = nodes[index];
  Matrix matrix{node.buf, node.base, node.n};
  for (size_t j = index + 1; j < nodes.size(); ++j) {
    const Node &later = nodes[j];
    if (later.kind == Node::Store && later.buf == node.buf)
      return false;
    if (later.kind == Node::MatVec &&
        Matrix{later.buf, later.base, later.n} == matrix)
      return true;
  }
  return false;
}

/// Which matrix slice runs the product at `index`, and whether it uses
/// stored columns.
MatMode Placer::decide(int index, int from) const {
  const Node &node = nodes[index];
  Matrix matrix{node.buf, node.base, node.n};
  for (const auto &entry : installed)
    if (entry.second == matrix)
      return {entry.first, true, false};
  int slice = nearest(mxms, from);
  if (node.n <= chip.mxmWeights && usedAgain(index))
    return {slice, true, true};
  return {slice, false, false};
}

/// Whether `node` may join a group that already reads the memory slices in
/// `readSlices`. `flight` is the value arriving from the previous operation
/// of the chain, or -1. On success the slices `node` reads are added.
bool Placer::admit(const Node &node, int flight, const MatMode &mode,
                   std::set<int> &readSlices) const {
  // The distinct words this operation reads from memory.
  std::set<Loc> words;
  for (int arg : node.args)
    if (arg != flight && valueLoc[arg])
      words.insert(*valueLoc[arg]);

  // The operands of a two-word operation or a select arrive on the same
  // cycle, so two of them cannot come from one slice. The operands of a
  // matrix-vector product arrive on different cycles.
  bool together = node.kind == Node::Bin || node.kind == Node::Sel;
  std::set<int> mine;
  for (const Loc &loc : words) {
    if (together && mine.count(loc.slice))
      return false;
    mine.insert(loc.slice);
  }
  if (node.kind == Node::MatVec && !mode.stored)
    mine.insert(bufLoc[node.buf].slice);

  for (int slice : mine)
    if (readSlices.count(slice))
      return false;
  readSlices.insert(mine.begin(), mine.end());
  return true;
}

/// A store to `buf` makes any stored copy of its columns stale.
void Placer::forget(int buf) {
  for (auto it = installed.begin(); it != installed.end();)
    it = it->second.buf == buf ? installed.erase(it) : std::next(it);
}

Operation *Placer::make(StringRef name, ArrayRef<Value> operands,
                        ArrayRef<Type> results,
                        ArrayRef<NamedAttribute> attrs) {
  OperationState state(func.getLoc(), name);
  state.addOperands(operands);
  state.addTypes(results);
  state.addAttributes(attrs);
  return builder.create(state);
}

Value Placer::emitRead(Loc loc) {
  return make("tau.i.read", {}, {word},
              {attr("slice", loc.slice), attr("addr", loc.addr)})
      ->getResult(0);
}

void Placer::emitWrite(Value value, Loc loc) {
  make("tau.i.write", {value}, {},
       {attr("slice", loc.slice), attr("addr", loc.addr)});
}

Error Placer::placeComputed(int index) {
  struct Member {
    int index;
    int slice;
    MatMode mode;
  };
  auto place = [&](int i, int from) {
    const Node &node = nodes[i];
    Member member{i, -1, {}};
    if (node.kind == Node::MatVec) {
      member.mode = decide(i, from);
      member.slice = member.mode.slice;
    } else {
      member.slice = sliceOf(node, from);
    }
    return member;
  };
  auto accept = [&](const Member &member) {
    const Node &node = nodes[member.index];
    if (node.kind == Node::MatVec && member.mode.stored)
      installed[member.slice] = Matrix{node.buf, node.base, node.n};
  };

  // The first operation. If operands that must arrive together sit in one
  // memory slice, copy all but one to scratch words in other slices.
  const Node &head = nodes[index];
  Member first = place(index, origin(head));
  std::set<int> readSlices;
  for (int attempt = 0; !admit(head, -1, first.mode, readSlices); ++attempt) {
    if (attempt >= 3)
      return createStringError("cannot place an operation");
    std::set<int> seen;
    std::set<int> taken;
    for (int arg : head.args)
      taken.insert(valueLoc[arg]->slice);
    int victim = -1;
    std::set<Loc> words;
    for (int arg : head.args) {
      Loc loc = *valueLoc[arg];
      if (!words.insert(loc).second)
        continue;
      if (!seen.insert(loc.slice).second) {
        victim = arg;
        break;
      }
    }
    if (victim < 0)
      return createStringError("cannot place an operation");
    Loc to = newScratch(taken);
    if (to.slice < 0)
      return createStringError(
          "an operation needs more memory slices than the chip has");
    emitCopy(*valueLoc[victim], to);
    valueLoc[victim] = to;
    readSlices.clear();
  }
  accept(first);

  // Grow the chain while each result feeds the next operation directly.
  std::vector<Member> chain{first};
  while (true) {
    int next = chainNext(chain.back().index);
    if (next < 0 || nodes[next].kind == Node::Store)
      break;
    Member member = place(next, chain.back().slice);
    if (!admit(nodes[next], nodes[chain.back().index].dst, member.mode,
               readSlices))
      break;
    accept(member);
    chain.push_back(member);
  }

  for (const Member &member : chain)
    if (member.slice < 0)
      return createStringError("the chip has no slice for an operation");

  // Columns to be stored are installed first, in a group of their own, on
  // consecutive cycles.
  for (const Member &member : chain) {
    const Node &node = nodes[member.index];
    if (node.kind != Node::MatVec || !member.mode.install)
      continue;
    Loc columns = bufLoc[node.buf];
    columns.addr += node.base;
    Value previous;
    for (int64_t j = 0; j < node.n; ++j) {
      SmallVector<Value> operands{emitRead({columns.slice, columns.addr + j})};
      if (previous)
        operands.push_back(previous);
      previous = make("tau.i.install", operands, {acc},
                      {attr("j", j), attr("slice", member.slice)})
                     ->getResult(0);
    }
  }

  // Emit the chain. `flight` is the previous result, on its way.
  Value flight;
  int flightValue = -1;
  for (const Member &member : chain) {
    const Node &node = nodes[member.index];
    int slice = member.slice;
    // A word needed twice by one operation is read once.
    std::map<Loc, Value> reads;
    auto operand = [&](int value) {
      if (value == flightValue)
        return flight;
      Loc loc = *valueLoc[value];
      auto found = reads.find(loc);
      if (found != reads.end())
        return found->second;
      return reads[loc] = emitRead(loc);
    };

    if (node.kind == Node::Un) {
      Value a = operand(node.args[0]);
      SmallVector<NamedAttribute> attrs{
          builder.getNamedAttr("fn", builder.getStringAttr(node.fn)),
          attr("slice", slice)};
      if (node.k)
        attrs.push_back(attr("k", *node.k));
      if (!node.table.empty())
        attrs.push_back(builder.getNamedAttr(
            "table", builder.getDenseI64ArrayAttr(node.table)));
      flight = make("tau.i.un", {a}, {word}, attrs)->getResult(0);
    } else if (node.kind == Node::Bin) {
      Value a = operand(node.args[0]);
      Value b = operand(node.args[1]);
      flight = make("tau.i.bin", {a, b}, {word},
                    {builder.getNamedAttr("fn", builder.getStringAttr(node.fn)),
                     attr("slice", slice)})
                   ->getResult(0);
    } else if (node.kind == Node::Sel) {
      Value m = operand(node.args[0]);
      Value a = operand(node.args[1]);
      Value b = operand(node.args[2]);
      flight =
          make("tau.i.sel", {m, a, b}, {word}, {attr("slice", slice)})
              ->getResult(0);
    } else if (node.kind == Node::Const) {
      flight = make("tau.i.const", {}, {word},
                    {builder.getNamedAttr(
                         "values", builder.getDenseI64ArrayAttr(node.values)),
                     attr("slice", slice)})
                   ->getResult(0);
    } else {
      // Matrix times vector: keep x, start from the bias if there is one,
      // then take one column per cycle.
      Value state = make("tau.i.load", {operand(node.args[0])}, {acc},
                         {attr("slice", slice)})
                        ->getResult(0);
      if (node.args.size() > 1)
        state = make("tau.i.seed", {state, operand(node.args[1])}, {acc},
                     {attr("slice", slice)})
                    ->getResult(0);
      Loc columns = bufLoc[node.buf];
      columns.addr += node.base;
      for (int64_t j = 0; j < node.n; ++j) {
        if (member.mode.stored) {
          state = make("tau.i.macw", {state}, {acc},
                       {attr("j", j), attr("slice", slice)})
                      ->getResult(0);
        } else {
          Value column = emitRead({columns.slice, columns.addr + j});
          state = make("tau.i.mac", {state, column}, {acc},
                       {attr("j", j), attr("slice", slice)})
                      ->getResult(0);
        }
      }
      flight =
          make("tau.i.emit", {state}, {word}, {attr("slice", slice)})
              ->getResult(0);
    }
    flightValue = node.dst;
    done[member.index] = true;
  }

  // Where the last result goes: the buffer the kernel stores it in, a
  // scratch word if it is needed later, or nowhere.
  int last = chain.back().index;
  int next = chainNext(last);
  if (next >= 0 && nodes[next].kind == Node::Store) {
    Loc target = bufLoc[nodes[next].buf];
    target.addr += nodes[next].base;
    emitWrite(flight, target);
    forget(nodes[next].buf);
    done[next] = true;
  } else if (!uses[flightValue].empty()) {
    Loc scratch = newScratch({});
    emitWrite(flight, scratch);
    valueLoc[flightValue] = scratch;
  }
  return Error::success();
}

Error Placer::run() {
  if (Error e = read())
    return e;

  int positions = static_cast<int>(chip.kinds.size());
  for (int p = 0; p < positions; ++p) {
    const std::string &kind = chip.kinds[p];
    if (kind == "mem")
      mems.push_back(p);
    else if (kind == "sxm")
      sxms.push_back(p);
    else if (kind == "mxm")
      mxms.push_back(p);
    else if (kind == "vxm" && vxm < 0)
      vxm = p;
  }
  if (mems.empty())
    return createStringError("the chip has no memory slice");

  // Buffers: spread over the memory slices in turn.
  used.assign(positions, 0);
  for (size_t b = 0; b < bufSizes.size(); ++b) {
    int slice = mems[b % mems.size()];
    bufLoc.push_back({slice, used[slice]});
    used[slice] += bufSizes[b];
  }

  // A virtual load needs no instruction of its own: its word is read from
  // the buffer wherever its value is used.
  for (int i = 0, e = static_cast<int>(nodes.size()); i < e; ++i)
    if (nodes[i].kind == Node::Load && isVirtual[i]) {
      Loc cell = bufLoc[nodes[i].buf];
      cell.addr += nodes[i].base;
      valueLoc[nodes[i].dst] = cell;
    }

  // New instructions go in front of the old operations, which are removed
  // at the end.
  Block &block = func.getBody().front();
  std::vector<Operation *> old;
  for (Operation &op : block)
    if (!isa<func::ReturnOp>(op))
      old.push_back(&op);
  builder.setInsertionPoint(block.getTerminator());
  word = tau::WordType::get(func.getContext());
  acc = tau::AccType::get(func.getContext());

  for (int i = 0, e = static_cast<int>(nodes.size()); i < e; ++i) {
    if (done[i])
      continue;
    const Node &node = nodes[i];
    Loc cell = node.buf >= 0 ? bufLoc[node.buf] : Loc{};
    cell.addr += node.base;

    if (node.kind == Node::Load) {
      if (!isVirtual[i]) {
        // A later store would overwrite the word, so take a copy now.
        Loc scratch = newScratch({});
        emitCopy(cell, scratch);
        valueLoc[node.dst] = scratch;
      }
    } else if (node.kind == Node::Store) {
      if (!valueLoc[node.args[0]])
        return createStringError("a stored value was never computed");
      emitCopy(*valueLoc[node.args[0]], cell);
      forget(node.buf);
    } else if (Error e = placeComputed(i)) {
      return e;
    }
    done[i] = true;
  }

  for (auto it = old.rbegin(); it != old.rend(); ++it)
    (*it)->erase();

  // Record what the later passes and the emitters need.
  tau::setChip(func, chip);
  func->setAttr("tau.mem_sizes", builder.getI64ArrayAttr(used));
  SmallVector<Attribute> map;
  for (size_t b = 0; b < bufSizes.size(); ++b)
    map.push_back(builder.getI64ArrayAttr(
        {bufLoc[b].slice, bufLoc[b].addr, bufSizes[b]}));
  func->setAttr("tau.map", builder.getArrayAttr(map));
  return Error::success();
}

struct PlacePass : PassWrapper<PlacePass, OperationPass<func::FuncOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(PlacePass)

  PlacePass(const tau::Chip &chip) : chip(chip) {}
  PlacePass(const PlacePass &other) : PassWrapper(other), chip(other.chip) {}

  StringRef getArgument() const final { return "tau-place"; }
  StringRef getDescription() const final {
    return "Choose slices and memory addresses and lower to instructions";
  }

  Option<std::string> chipFile{
      *this, "chip",
      llvm::cl::desc("Chip description (JSON); default: the standard chip")};

  void runOnOperation() override {
    tau::Chip target = chip;
    if (!chipFile.empty()) {
      Expected<tau::Chip> read = tau::Chip::fromFile(chipFile);
      if (!read) {
        getOperation().emitError(toString(read.takeError()));
        return signalPassFailure();
      }
      target = std::move(*read);
    }
    Placer placer(getOperation(), target);
    if (Error e = placer.run()) {
      getOperation().emitError(toString(std::move(e)));
      signalPassFailure();
    }
  }

  tau::Chip chip;
};

} // namespace

std::unique_ptr<Pass> tau::createPlacePass(const Chip &chip) {
  return std::make_unique<PlacePass>(chip);
}
