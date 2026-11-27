//===- Place.cpp - the tau-place pass -------------------------------------===//
//
// Turns a kernel with no loops into instructions, and decides where
// (Compiler 4): which memory holds each buffer, and which slice runs each
// operation. In textbook terms this is *binding*.
//
// Buffers. Buffers are spread over the memory slices in turn. The memories
// hold the buffers and nothing else: scratch space is `tau-schedule`'s to
// add.
//
// Operations. An operation runs on a slice of the kind it needs. Where the
// machine has several, it takes the one nearest to the slice its first
// operand comes from.
//
// Stored matrices. A matrix slice can keep the columns of a matrix. When the
// same matrix is multiplied again later, with no store to its buffer in
// between, the pass installs the columns once and every product then uses
// the stored columns instead of streaming them from memory again. Which
// slice stores which matrix is a decision about where.
//
// Each operation of the kernel becomes its instructions, in the kernel's
// order: a load one read, a store one write, a matrix product the
// instructions of its matrix slice with a read for each column it streams,
// and any other operation one instruction. A word goes from the instruction
// that makes it to every instruction that uses it. The pass decides nothing
// about time: no word waits in memory here, and no rule in this file exists
// to make a schedule possible.
//
// Pins. A pinned operation hands its pin to the instruction that issues its
// word: the read of a load, the write of a store, the `emit` of a matrix
// product, and otherwise the one instruction the operation becomes.
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

#include <map>
#include <optional>

using namespace llvm;
using namespace mlir;

namespace {

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
  Type accType;

  std::vector<Node> nodes;
  std::vector<int64_t> bufSizes;

  /// The positions of the slices of each kind.
  std::vector<int> mems, vxms, sxms, mxms;
  /// For each buffer, its memory slice and first address.
  std::vector<std::pair<int, int64_t>> bufLoc;
  /// For each value of the kernel, the word that carries it.
  std::vector<Value> words;
  /// The matrix whose columns each matrix slice currently stores.
  std::map<int, Matrix> installed;
  /// The location given to new instructions: that of the operation being
  /// placed.
  Location here;

  bool read();
  bool usedAgain(size_t index) const;
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
    Node node(op.getLoc());
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
  words.assign(values.size(), Value());
  return true;
}

/// Whether the matrix of the product at `index` is multiplied again later,
/// before anything is stored to its buffer.
bool Placer::usedAgain(size_t index) const {
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
        tau::intAttr(*words[node.args[0]].getDefiningOp(), "slice"));
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

/// A read of the word at `position` of buffer `buf`.
Value Placer::readWord(int buf, int64_t position) {
  return make("tau.i.read", {}, {wordType},
              {attr("slice", bufLoc[buf].first),
               attr("addr", bufLoc[buf].second + position)})
      ->getResult(0);
}

/// Matrix times vector: keep `x`, start from the bias if there is one, take
/// one column per instruction, and give the accumulator.
bool Placer::placeProduct(size_t index) {
  const Node &node = nodes[index];
  Matrix matrix{node.buf, node.base, node.n};

  // The slice: the one that already stores the columns, or the nearest.
  int slice = -1;
  bool stored = false;
  for (const auto &entry : installed)
    if (entry.second == matrix) {
      slice = entry.first;
      stored = true;
    }
  if (slice < 0) {
    slice = nearest(mxms, cameFrom(node));
    if (slice < 0) {
      emitError(node.loc, "the machine has no matrix slice for this product");
      return false;
    }
    // Store the columns first if the matrix is used again.
    if (node.n <= machine.mxmWeights && usedAgain(index)) {
      Value previous;
      for (int64_t j = 0; j < node.n; ++j) {
        SmallVector<Value> operands{readWord(node.buf, node.base + j)};
        if (previous)
          operands.push_back(previous);
        previous = make("tau.i.install", operands, {accType},
                        {attr("j", j), attr("slice", slice)})
                       ->getResult(0);
      }
      installed[slice] = matrix;
      stored = true;
    }
  }

  Value state = make("tau.i.load", {words[node.args[0]]}, {accType},
                     {attr("slice", slice)})
                    ->getResult(0);
  if (node.args.size() > 1)
    state = make("tau.i.seed", {state, words[node.args[1]]}, {accType},
                 {attr("slice", slice)})
                ->getResult(0);
  for (int64_t j = 0; j < node.n; ++j) {
    if (stored) {
      state = make("tau.i.macw", {state}, {accType},
                   {attr("j", j), attr("slice", slice)})
                  ->getResult(0);
    } else {
      Value column = readWord(node.buf, node.base + j);
      state = make("tau.i.mac", {state, column}, {accType},
                   {attr("j", j), attr("slice", slice)})
                  ->getResult(0);
    }
  }
  words[node.dst] =
      make("tau.i.emit", {state}, {wordType}, {attr("slice", slice)})
          ->getResult(0);
  return true;
}

/// The instructions of one operation of the kernel.
bool Placer::place(size_t index) {
  const Node &node = nodes[index];
  here = node.loc;
  Operation *issuer = nullptr;

  switch (node.kind) {
  case Node::Load:
    words[node.dst] = readWord(node.buf, node.base);
    issuer = words[node.dst].getDefiningOp();
    break;
  case Node::Store:
    issuer = make("tau.i.write", {words[node.args[0]]}, {},
                  {attr("slice", bufLoc[node.buf].first),
                   attr("addr", bufLoc[node.buf].second + node.base)});
    // A store makes any stored copy of the buffer's columns stale.
    for (auto it = installed.begin(); it != installed.end();)
      it = it->second.buf == node.buf ? installed.erase(it) : std::next(it);
    break;
  case Node::MatVec:
    if (!placeProduct(index))
      return false;
    issuer = words[node.dst].getDefiningOp();
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
      operands.push_back(words[arg]);
    SmallVector<NamedAttribute> attrs{attr("slice", slice)};
    StringRef name;
    if (node.kind == Node::Un) {
      name = "tau.i.un";
      attrs.push_back(builder.getNamedAttr("fn", builder.getStringAttr(node.fn)));
      if (node.k)
        attrs.push_back(attr("k", *node.k));
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
    issuer = make(name, operands, {wordType}, attrs);
    words[node.dst] = issuer->getResult(0);
    break;
  }
  }
  if (node.pin)
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

  // Buffers: spread over the memory slices in turn.
  std::vector<int64_t> used(positions, 0);
  for (size_t b = 0; b < bufSizes.size(); ++b) {
    int slice = mems[b % mems.size()];
    bufLoc.push_back({slice, used[slice]});
    used[slice] += bufSizes[b];
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
  accType = tau::AccType::get(func.getContext());
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
  for (size_t b = 0; b < bufSizes.size(); ++b)
    map.push_back(builder.getI64ArrayAttr(
        {bufLoc[b].first, bufLoc[b].second, bufSizes[b]}));
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
