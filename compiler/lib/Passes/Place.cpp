//===- Place.cpp - the tau-place pass -------------------------------------===//
//
// Turns a kernel with no loops into instructions, and decides where
// (Compiler 4): which memory holds each buffer, and which slice runs each
// operation. In textbook terms this is *binding*.
//
// Values. A value of the kernel becomes its words, one, two or four of them
// (Machine 1). A load is a read for each word and a store a write for each;
// an operation of the vector or rearrangement slice is one instruction that
// takes and gives words.
//
// Buffers. Buffers are spread over the memory slices in turn, each in the
// lower bank of its slice (Machine 3.11). A buffer of values of several
// words is dealt out over as many memory slices that are next to one
// another (Compiler 3): the words of a value are then in different slices,
// on one side of whatever uses them. A buffer that holds a matrix is dealt
// out over several memory slices too, so that several of its words can be
// read on one cycle. The memories hold the buffers and nothing else: scratch
// space is `tau-schedule`'s to add, and it adds it in the upper bank, so
// that a word can be put away while a buffer is read.
//
// Operations. An operation runs on a slice of the kind it needs. Where the
// machine has several, it takes the one nearest to the slice its first
// operand comes from.
//
// Matrices. A matrix slice multiplies by the words installed in it. The pass
// installs the words of a matrix, each read from its buffer, before the
// first product with it. One `install` takes as many words as follow one
// another in different memory slices on one side of the matrix slice: those
// can arrive together. A later product with the same matrix, with no
// store to its buffer and no other matrix installed in the slice in
// between, uses the words that are there. Which slice holds which matrix is
// a decision about where.
//
// Each operation of the kernel becomes its instructions, in the kernel's
// order: a load its reads, a store its writes, a matrix product one
// `product`, after a read and an `install` for each word of a matrix that is
// not installed yet, and any other operation one instruction. A word goes
// from the instruction that makes it to every instruction that uses it. The
// pass decides nothing about time: no word waits in memory here, and no rule
// in this file exists to make a schedule possible.
//
// Pins. A pinned operation hands its pin to the instruction that issues its
// value: the reads of a load, the writes of a store, the `product` of a
// matrix product, and otherwise the one instruction the operation becomes.
//
// The pass records the machine, the memory map and the memory sizes on the
// function.
//
// Nothing here is proved. `tau-check unrolled.json placed.json` decides whether
// the instructions, run in order, compute what the kernel computes, and
// `tau-check --decides` whether the pass kept to deciding where.
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

#include <limits>
#include <map>
#include <optional>
#include <set>

using namespace llvm;
using namespace mlir;

namespace {

/// A matrix: `n` words of a buffer starting at `base`.
struct Matrix {
  int buf;
  int64_t base;
  int64_t n;

  bool operator==(const Matrix &other) const {
    return buf == other.buf && base == other.base && n == other.n;
  }
};

/// Where a buffer lives (Compiler 3): its parts, each a memory slice and the
/// address of the part's first word, and the number of its words. The words
/// are dealt out over the parts in turn.
struct Home {
  std::vector<std::pair<int, int64_t>> parts;
  int64_t size = 0;

  /// The slice and the address of word `k`.
  std::pair<int, int64_t> locate(int64_t k) const {
    int64_t g = static_cast<int64_t>(parts.size());
    return {parts[k % g].first, parts[k % g].second + k / g};
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
  /// `Sel` (mask first), and the vector for `MatVec`.
  std::vector<int> args;
  int buf = -1;
  int64_t base = 0;
  int64_t n = 0;
  /// The bits of the values the operation takes, and of the one it gives.
  int64_t bits = 8;
  int64_t outBits = 8;
  /// The cycle the operation's word must be issued on, if it is pinned.
  std::optional<int64_t> pin;
  /// Where the operation is in the user's file, for error messages.
  Location loc;

  Node(Location loc) : loc(loc) {}
};

class Placer {
public:
  Placer(func::FuncOp func, const tau::Machine &machine)
      : func(func), machine(machine), builder(func.getContext()),
        here(func.getLoc()) {}

  /// False if the kernel cannot be placed; the error has been reported.
  bool run();

private:
  func::FuncOp func;
  const tau::Machine &machine;
  OpBuilder builder;
  Type wordType;
  Type planeType;

  std::vector<Node> nodes;
  /// For each buffer, the number of its words and of the words in one of
  /// its values.
  std::vector<int64_t> bufSizes;
  std::vector<int64_t> bufWords;

  /// The positions of the slices of each kind.
  std::vector<int> mems, vxms, sxms, mxms;
  /// For each buffer, where it lives.
  std::vector<Home> homes;
  /// For each value of the kernel, the words that carry it, the low word
  /// first.
  std::vector<SmallVector<Value, 4>> words;
  /// The matrix whose words each matrix slice has installed.
  std::map<int, Matrix> installed;
  /// The location given to new instructions: that of the operation being
  /// placed.
  Location here;

  bool read();
  static int nearest(const std::vector<int> &candidates, int from);
  int cameFrom(const Node &node) const;

  Operation *make(StringRef name, ArrayRef<Value> operands,
                  ArrayRef<Type> results, ArrayRef<NamedAttribute> attrs);
  NamedAttribute attr(StringRef name, int64_t value) {
    return builder.getNamedAttr(name, builder.getI64IntegerAttr(value));
  }
  Value readWord(int buf, int64_t position);
  bool place(size_t index);
  bool placeProduct(size_t index);
};

bool Placer::read() {
  llvm::DenseMap<Value, int> buffers;
  llvm::DenseMap<Value, int> values;
  for (BlockArgument arg : func.getArguments()) {
    auto buf = dyn_cast<tau::BufType>(arg.getType());
    if (!buf) {
      func.emitError("every argument must be a !tau.buf");
      return false;
    }
    buffers[arg] = static_cast<int>(bufSizes.size());
    bufWords.push_back(tau::wordsOf(buf.getBits()));
    bufSizes.push_back(buf.getSize() * bufWords.back());
  }
  auto define = [&](Value value) {
    int id = static_cast<int>(values.size());
    values[value] = id;
    return id;
  };

  auto bitsOf = [](Value value) {
    return static_cast<int64_t>(cast<tau::IntType>(value.getType()).getBits());
  };
  for (Operation &op : func.getBody().front()) {
    if (isa<func::ReturnOp>(op))
      continue;
    Node node(op.getLoc());
    if (op.getNumOperands() > 0 && isa<tau::IntType>(op.getOperand(0).getType()))
      node.bits = bitsOf(op.getOperand(0));
    if (op.getNumResults() > 0)
      node.outBits = bitsOf(op.getResult(0));
    if (op.getNumOperands() == 0 || isa<tau::LoadOp>(op))
      node.bits = node.outBits;
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
      op.emitError("run tau-unroll before tau-place");
      return false;
    } else if (isa<tau::CallOp>(op)) {
      op.emitError("run tau-inline before tau-place");
      return false;
    } else {
      op.emitError("cannot place this operation");
      return false;
    }
    if (auto at = op.getAttrOfType<IntegerAttr>("at"))
      node.pin = at.getInt();
    nodes.push_back(std::move(node));
  }
  words.assign(values.size(), {});
  return true;
}

/// The candidate nearest to `from`; the first of them on a tie. -1 if there
/// is none.
int Placer::nearest(const std::vector<int> &candidates, int from) {
  int best = -1;
  for (int candidate : candidates)
    if (best < 0 || std::abs(candidate - from) < std::abs(best - from))
      best = candidate;
  return best;
}

/// The slice the first operand of an operation comes from. An operation
/// with no operand counts as coming from the first vector slice.
int Placer::cameFrom(const Node &node) const {
  if (!node.args.empty())
    return static_cast<int>(
        tau::intAttr(*words[node.args[0]].front().getDefiningOp(), "slice"));
  return vxms.empty() ? 0 : vxms.front();
}

Operation *Placer::make(StringRef name, ArrayRef<Value> operands,
                        ArrayRef<Type> results,
                        ArrayRef<NamedAttribute> attrs) {
  OperationState state(here, name);
  state.addOperands(operands);
  state.addTypes(results);
  state.addAttributes(attrs);
  return builder.create(state);
}

/// A read of word `position` of buffer `buf`.
Value Placer::readWord(int buf, int64_t position) {
  auto [slice, addr] = homes[buf].locate(position);
  return make("tau.i.read", {}, {wordType},
              {attr("slice", slice), attr("addr", addr)})
      ->getResult(0);
}

/// Matrix times vector: install the words of the matrix, unless the slice
/// has them, and multiply.
bool Placer::placeProduct(size_t index) {
  const Node &node = nodes[index];
  Matrix matrix{node.buf, node.base, node.n};
  if (node.n > machine.lanes) {
    emitError(node.loc, "a matrix of ")
        << node.n << " words does not fit: a matrix slice holds "
        << machine.lanes;
    return false;
  }

  // The slice: one that has the words installed, or the nearest.
  int slice = -1;
  for (const auto &entry : installed)
    if (entry.second == matrix)
      slice = entry.first;
  if (slice < 0) {
    slice = nearest(mxms, cameFrom(node));
    if (slice < 0) {
      emitError(node.loc, "the machine has no matrix slice for this product");
      return false;
    }
    Value previous;
    for (int64_t j = 0; j < node.n;) {
      // The words of one `install`: as many as follow one another in
      // different memory slices on one side of the matrix slice.
      SmallVector<Value> operands;
      std::set<int> from;
      bool east = false;
      int64_t g = 0;
      while (j + g < node.n && g < machine.streams) {
        int mem = homes[node.buf].locate(node.base + j + g).first;
        if (g > 0 && (from.count(mem) || (mem > slice) != east))
          break;
        east = mem > slice;
        from.insert(mem);
        operands.push_back(readWord(node.buf, node.base + j + g));
        ++g;
      }
      if (previous)
        operands.push_back(previous);
      previous = make("tau.i.install", operands, {planeType},
                      {attr("j", j), attr("slice", slice)})
                     ->getResult(0);
      j += g;
    }
    installed[slice] = matrix;
  }

  SmallVector<Type> product(tau::wordsOf(node.outBits), wordType);
  Operation *op = make("tau.i.product", {words[node.args[0]].front()}, product,
                       {attr("n", node.n), attr("slice", slice)});
  words[node.dst].assign(op->result_begin(), op->result_end());
  return true;
}

/// The instructions of one operation of the kernel.
bool Placer::place(size_t index) {
  const Node &node = nodes[index];
  here = node.loc;
  // The instructions that issue the value of the operation: a pin goes on
  // each of them.
  SmallVector<Operation *> issuers;

  switch (node.kind) {
  case Node::Load:
    for (int64_t k = 0, w = bufWords[node.buf]; k < w; ++k) {
      words[node.dst].push_back(readWord(node.buf, w * node.base + k));
      issuers.push_back(words[node.dst].back().getDefiningOp());
    }
    break;
  case Node::Store:
    for (int64_t k = 0, w = bufWords[node.buf]; k < w; ++k) {
      auto [slice, addr] = homes[node.buf].locate(w * node.base + k);
      issuers.push_back(make("tau.i.write", {words[node.args[0]][k]}, {},
                             {attr("slice", slice), attr("addr", addr)}));
    }
    // A store makes the installed words of the buffer stale.
    for (auto it = installed.begin(); it != installed.end();)
      it = it->second.buf == node.buf ? installed.erase(it) : std::next(it);
    break;
  case Node::MatVec:
    if (!placeProduct(index))
      return false;
    issuers.push_back(words[node.dst].front().getDefiningOp());
    break;
  case Node::Un:
  case Node::Bin:
  case Node::Sel:
  case Node::Const: {
    bool rearrangement =
        node.kind == Node::Un && tau::isRearrangement(node.fn);
    int slice = nearest(rearrangement ? sxms : vxms, cameFrom(node));
    if (slice < 0) {
      emitError(node.loc, "the machine has no ")
          << (rearrangement ? "rearrangement" : "vector")
          << " slice for this operation";
      return false;
    }
    SmallVector<Value> operands;
    for (int arg : node.args)
      operands.append(words[arg].begin(), words[arg].end());
    SmallVector<NamedAttribute> attrs{attr("slice", slice),
                                      attr("bits", node.bits)};
    StringRef name;
    if (node.kind == Node::Un) {
      name = "tau.i.un";
      attrs.push_back(builder.getNamedAttr("fn", builder.getStringAttr(node.fn)));
      if (node.k)
        attrs.push_back(attr("k", *node.k));
      if (node.fn == "widen")
        attrs.push_back(attr("to", node.outBits));
      if (!node.table.empty())
        attrs.push_back(builder.getNamedAttr(
            "table", builder.getDenseI64ArrayAttr(node.table)));
    } else if (node.kind == Node::Bin) {
      name = "tau.i.bin";
      attrs.push_back(builder.getNamedAttr("fn", builder.getStringAttr(node.fn)));
    } else if (node.kind == Node::Sel) {
      name = "tau.i.sel";
    } else {
      name = "tau.i.const";
      attrs.push_back(builder.getNamedAttr(
          "values", builder.getDenseI64ArrayAttr(node.values)));
    }
    SmallVector<Type> results(tau::wordsOf(node.outBits), wordType);
    Operation *op = make(name, operands, results, attrs);
    words[node.dst].assign(op->result_begin(), op->result_end());
    issuers.push_back(op);
    break;
  }
  }
  if (node.pin)
    for (Operation *issuer : issuers)
      tau::setIntAttr(*issuer, "pin", *node.pin);
  return true;
}

bool Placer::run() {
  if (!read())
    return false;

  int positions = static_cast<int>(machine.kinds.size());
  for (int p = 0; p < positions; ++p) {
    const std::string &kind = machine.kinds[p];
    (kind == "mem" ? mems : kind == "vxm" ? vxms : kind == "sxm" ? sxms : mxms)
        .push_back(p);
  }
  if (mems.empty()) {
    func.emitError("the machine has no memory slice");
    return false;
  }

  // The runs of memory slices that are next to one another.
  std::vector<std::vector<int>> runs;
  for (int mem : mems) {
    if (runs.empty() || runs.back().back() + 1 != mem)
      runs.emplace_back();
    runs.back().push_back(mem);
  }

  // Buffers: spread over the memory slices in turn.
  std::set<int> matrices;
  for (const Node &node : nodes)
    if (node.kind == Node::MatVec)
      matrices.insert(node.buf);
  std::vector<int64_t> used(positions, 0);
  for (size_t b = 0; b < bufSizes.size(); ++b) {
    Home home;
    home.size = bufSizes[b];
    std::vector<int> slices{mems[b % mems.size()]};
    if (bufWords[b] > 1) {
      // Values of several words: as many slices next to one another, so
      // that the words of a value are in different slices on one side of
      // whatever uses them. Of the runs that are long enough, in turn, the
      // stretch with the fewest words in it so far.
      size_t width = static_cast<size_t>(bufWords[b]);
      const std::vector<int> *run = nullptr;
      for (size_t r = 0; r < runs.size() && !run; ++r)
        if (runs[(b + r) % runs.size()].size() >= width)
          run = &runs[(b + r) % runs.size()];
      if (!run) {
        func.emitError("a buffer of values of ")
            << width << " words needs " << width
            << " memory slices next to one another";
        return false;
      }
      size_t best = 0;
      int64_t least = std::numeric_limits<int64_t>::max();
      for (size_t from = 0; from + width <= run->size(); ++from) {
        int64_t total = 0;
        for (size_t i = 0; i < width; ++i)
          total += used[(*run)[from + i]];
        if (total < least) {
          least = total;
          best = from;
        }
      }
      slices.assign(run->begin() + best, run->begin() + best + width);
    } else if (matrices.count(static_cast<int>(b))) {
      // A matrix is dealt out over several slices if that brings its words
      // to a matrix slice sooner: over `g` slices the words leave memory in
      // `size / g` cycles, rounded up, and the last of them has further to
      // go by the distance between the first slice and the last.
      int64_t most = std::min<int64_t>(
          {static_cast<int64_t>(mems.size()), machine.streams, home.size});
      int64_t best = home.size, g = 1;
      int low = slices.front(), high = low;
      for (int64_t parts = 2; parts <= most; ++parts) {
        int slice = mems[(b + parts - 1) % mems.size()];
        low = std::min(low, slice);
        high = std::max(high, slice);
        int64_t cost = (home.size + parts - 1) / parts + (high - low);
        if (cost < best) {
          best = cost;
          g = parts;
        }
      }
      for (int64_t i = 1; i < g; ++i)
        slices.push_back(mems[(b + i) % mems.size()]);
    }
    int64_t g = static_cast<int64_t>(slices.size());
    for (int64_t i = 0; i < g; ++i) {
      int slice = slices[i];
      home.parts.push_back({slice, used[slice]});
      // Part `i` holds the words `i`, `i + g`, `i + 2g`, ...
      used[slice] += (home.size - i + g - 1) / g;
      if (used[slice] > machine.bankSize) {
        func.emitError(
            "the buffers do not fit: the lower bank of memory slice ")
            << slice << " holds " << machine.bankSize << " words";
        return false;
      }
    }
    homes.push_back(std::move(home));
  }

  // New instructions go in front of the old operations, which are removed
  // at the end.
  Block &block = func.getBody().front();
  std::vector<Operation *> old;
  for (Operation &op : block)
    if (!isa<func::ReturnOp>(op))
      old.push_back(&op);
  builder.setInsertionPoint(block.getTerminator());
  wordType = tau::WordType::get(func.getContext());
  planeType = tau::PlaneType::get(func.getContext());
  here = func.getLoc();

  for (size_t i = 0; i < nodes.size(); ++i)
    if (!place(i))
      return false;

  for (auto it = old.rbegin(); it != old.rend(); ++it)
    (*it)->erase();

  // Record what the later passes and the emitters need.
  tau::setMachine(func, machine);
  func->setAttr("tau.mem_sizes", builder.getI64ArrayAttr(used));
  SmallVector<Attribute> map;
  for (const Home &home : homes) {
    // The size, then each part's slice and first address.
    SmallVector<int64_t> numbers{home.size};
    for (auto [slice, base] : home.parts) {
      numbers.push_back(slice);
      numbers.push_back(base);
    }
    map.push_back(builder.getI64ArrayAttr(numbers));
  }
  func->setAttr("tau.map", builder.getArrayAttr(map));
  return true;
}

struct PlacePass : PassWrapper<PlacePass, OperationPass<func::FuncOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(PlacePass)

  PlacePass(const tau::Machine &machine) : machine(machine) {}
  PlacePass(const PlacePass &other) : PassWrapper(other), machine(other.machine) {}

  StringRef getArgument() const final { return "tau-place"; }
  StringRef getDescription() const final {
    return "Choose slices and memory addresses and lower to instructions";
  }

  Option<std::string> machineFile{
      *this, "machine",
      llvm::cl::desc("Machine description (JSON); default: the standard machine")};

  void runOnOperation() override {
    tau::Machine target = machine;
    if (!machineFile.empty()) {
      Expected<tau::Machine> read = tau::Machine::fromFile(machineFile);
      if (!read) {
        getOperation().emitError(toString(read.takeError()));
        return signalPassFailure();
      }
      target = std::move(*read);
    }
    Placer placer(getOperation(), target);
    if (!placer.run())
      signalPassFailure();
  }

  tau::Machine machine;
};

} // namespace

std::unique_ptr<Pass> tau::createPlacePass(const Machine &machine) {
  return std::make_unique<PlacePass>(machine);
}
