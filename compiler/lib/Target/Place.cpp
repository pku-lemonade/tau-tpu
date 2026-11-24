//===- Place.cpp - the tau-place pass -------------------------------------===//
//
// Turns a kernel with no loops into instructions.
//
// Placement of buffers. Buffers are spread over the memory slices in turn.
// Words of memory beyond the buffers are scratch space.
//
// Placement of operations. Every operation runs on the first slice of the
// kind it needs.
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
//   * the two operands of an operation are not read from the same slice.
//
// When the second condition fails for a single operation, one operand is
// first copied to a scratch word in another slice.
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

#include <optional>
#include <set>

using namespace llvm;
using namespace mlir;

namespace {

/// A word of memory.
struct Loc {
  int slice = -1;
  int64_t addr = 0;
};

/// One operation of the kernel, with values and buffers as numbers.
struct Node {
  enum Kind { Load, Store, Un, Bin, MatVec } kind;
  std::string fn;
  std::optional<int64_t> k;
  int dst = -1;
  int a = -1;
  int b = -1;
  int buf = -1;
  int64_t base = 0;
  int64_t n = 0;
};

/// "tau.relu" -> "relu".
StringRef shortName(Operation &op) {
  return op.getName().getStringRef().drop_front(strlen("tau."));
}

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
  int vxm = -1;
  int sxm = -1;
  int mxm = -1;
  /// Words of memory handed out so far at each position.
  std::vector<int64_t> used;
  std::vector<Loc> bufLoc;
  size_t nextScratch = 0;

  /// Where each value can be read from memory, once it can.
  std::vector<std::optional<Loc>> valueLoc;
  std::vector<bool> done;

  Error read();
  int sliceOf(const Node &node) const;
  Loc newScratch(int avoid);
  int chainNext(int index) const;
  bool admit(const Node &node, int flight, std::set<int> &readSlices) const;
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
      node.a = values.lookup(store.getValue());
      node.buf = buffers.lookup(store.getBuf());
      node.base = store.getBase();
    } else if (auto matvec = dyn_cast<tau::MatVecOp>(op)) {
      node.kind = Node::MatVec;
      node.a = values.lookup(matvec.getX());
      node.buf = buffers.lookup(matvec.getBuf());
      node.base = matvec.getBase();
      node.n = matvec.getN();
      node.dst = define(matvec.getResult());
    } else if (isa<tau::AddOp, tau::SubOp, tau::MulOp, tau::MaxOp,
                   tau::MinOp>(op)) {
      node.kind = Node::Bin;
      node.fn = shortName(op).str();
      node.a = values.lookup(op.getOperand(0));
      node.b = values.lookup(op.getOperand(1));
      node.dst = define(op.getResult(0));
    } else if (isa<tau::ReluOp, tau::RequantOp, tau::ShiftOp,
                   tau::RotateOp>(op)) {
      node.kind = Node::Un;
      node.fn = shortName(op).str();
      if (auto k = op.getAttrOfType<IntegerAttr>("k"))
        node.k = k.getInt();
      node.a = values.lookup(op.getOperand(0));
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
  for (int i = 0, e = static_cast<int>(nodes.size()); i < e; ++i) {
    if (nodes[i].a >= 0)
      uses[nodes[i].a].push_back(i);
    if (nodes[i].b >= 0)
      uses[nodes[i].b].push_back(i);
  }

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

int Placer::sliceOf(const Node &node) const {
  switch (node.kind) {
  case Node::Bin:
    return vxm;
  case Node::MatVec:
    return mxm;
  case Node::Un:
    return (node.fn == "shift" || node.fn == "rotate") ? sxm : vxm;
  default:
    return -1;
  }
}

Loc Placer::newScratch(int avoid) {
  for (size_t tries = 0; tries < mems.size(); ++tries) {
    int slice = mems[(nextScratch + tries) % mems.size()];
    if (slice == avoid)
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

/// Whether `node` may join a group that already reads the memory slices in
/// `readSlices`. `flight` is the value arriving from the previous operation
/// of the chain, or -1. On success the slices `node` reads are added.
bool Placer::admit(const Node &node, int flight,
                   std::set<int> &readSlices) const {
  std::set<int> mine;
  auto fromMemory = [&](int value) -> std::optional<Loc> {
    if (value < 0 || value == flight)
      return std::nullopt;
    return valueLoc[value];
  };
  std::optional<Loc> a = fromMemory(node.a);
  std::optional<Loc> b = node.b == node.a ? std::nullopt : fromMemory(node.b);
  if (a)
    mine.insert(a->slice);
  if (b) {
    // Two different words from one slice would have to be read on the same
    // cycle.
    if (a && a->slice == b->slice)
      return false;
    mine.insert(b->slice);
  }
  if (node.kind == Node::MatVec)
    mine.insert(bufLoc[node.buf].slice);
  for (int slice : mine)
    if (readSlices.count(slice))
      return false;
  readSlices.insert(mine.begin(), mine.end());
  return true;
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
  // A single operation whose two operands sit in one memory slice: copy one
  // of them to another slice first.
  const Node &head = nodes[index];
  std::set<int> readSlices;
  if (!admit(head, -1, readSlices)) {
    Loc from = *valueLoc[head.b];
    Loc to = newScratch(from.slice);
    if (to.slice < 0)
      return createStringError(
          "an operation needs two memory slices, and the chip has one");
    emitCopy(from, to);
    valueLoc[head.b] = to;
    readSlices.clear();
    if (!admit(head, -1, readSlices))
      return createStringError("cannot place an operation");
  }

  // Grow the chain while each result feeds the next operation directly.
  std::vector<int> chain{index};
  while (true) {
    int next = chainNext(chain.back());
    if (next < 0 || nodes[next].kind == Node::Store)
      break;
    if (!admit(nodes[next], nodes[chain.back()].dst, readSlices))
      break;
    chain.push_back(next);
  }

  // Emit the chain. `flight` is the previous result, on its way.
  Value flight;
  int flightValue = -1;
  for (int member : chain) {
    const Node &node = nodes[member];
    int slice = sliceOf(node);
    if (slice < 0)
      return createStringError("the chip has no slice for '" + node.fn + "'");
    auto operand = [&](int value) {
      return value == flightValue ? flight : emitRead(*valueLoc[value]);
    };

    if (node.kind == Node::Un) {
      Value a = operand(node.a);
      SmallVector<NamedAttribute> attrs{
          builder.getNamedAttr("fn", builder.getStringAttr(node.fn)),
          attr("slice", slice)};
      if (node.k)
        attrs.push_back(attr("k", *node.k));
      flight = make("tau.i.un", {a}, {word}, attrs)->getResult(0);
    } else if (node.kind == Node::Bin) {
      Value a = operand(node.a);
      Value b = node.b == node.a ? a : operand(node.b);
      // One travelling word cannot be used twice, so `f(a, a)` reads `a`
      // once only when it comes from memory, where a second read is free.
      if (node.b == node.a && node.a != flightValue)
        b = a;
      flight = make("tau.i.bin", {a, b}, {word},
                    {builder.getNamedAttr("fn", builder.getStringAttr(node.fn)),
                     attr("slice", slice)})
                   ->getResult(0);
    } else {
      Value x = operand(node.a);
      Value state =
          make("tau.i.load", {x}, {acc}, {attr("slice", slice)})->getResult(0);
      Loc columns = bufLoc[node.buf];
      columns.addr += node.base;
      for (int64_t j = 0; j < node.n; ++j) {
        Value column = emitRead({columns.slice, columns.addr + j});
        state = make("tau.i.mac", {state, column}, {acc},
                     {attr("j", j), attr("slice", slice)})
                    ->getResult(0);
      }
      flight =
          make("tau.i.emit", {state}, {word}, {attr("slice", slice)})
              ->getResult(0);
    }
    flightValue = node.dst;
    done[member] = true;
  }

  // Where the last result goes: the buffer the kernel stores it in, a
  // scratch word if it is needed later, or nowhere.
  int last = chain.back();
  int next = chainNext(last);
  if (next >= 0 && nodes[next].kind == Node::Store) {
    Loc target = bufLoc[nodes[next].buf];
    target.addr += nodes[next].base;
    emitWrite(flight, target);
    done[next] = true;
  } else if (!uses[flightValue].empty()) {
    Loc scratch = newScratch(-1);
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
    else if (kind == "vxm" && vxm < 0)
      vxm = p;
    else if (kind == "sxm" && sxm < 0)
      sxm = p;
    else if (kind == "mxm" && mxm < 0)
      mxm = p;
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
        Loc scratch = newScratch(-1);
        emitCopy(cell, scratch);
        valueLoc[node.dst] = scratch;
      }
    } else if (node.kind == Node::Store) {
      if (!valueLoc[node.a])
        return createStringError("a stored value was never computed");
      emitCopy(*valueLoc[node.a], cell);
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
