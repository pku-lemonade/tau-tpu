//===- EmitKernel.cpp - write a function as a kernel file -----------------===//
//
// Writes the function the user wrote in the JSON form that the Lean tools
// read (Tau/Sim/Json.lean). Buffers are numbered by argument position and
// values in order of definition.
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Target/Target.h"

#include "llvm/ADT/DenseMap.h"

using namespace llvm;
using namespace mlir;

namespace {

struct Numbering {
  llvm::DenseMap<Value, int64_t> buffers;
  llvm::DenseMap<Value, int64_t> values;

  int64_t define(Value value) {
    int64_t id = static_cast<int64_t>(values.size());
    values[value] = id;
    return id;
  }
};

Expected<json::Value> emitStmt(Operation &op, Numbering &num) {
  if (auto load = dyn_cast<tau::LoadOp>(op))
    return json::Object{{"op", "load"},
                        {"dst", num.define(load.getResult())},
                        {"buf", num.buffers.lookup(load.getBuf())},
                        {"base", static_cast<int64_t>(load.getBase())},
                        {"stride", static_cast<int64_t>(load.getStride())}};
  if (auto store = dyn_cast<tau::StoreOp>(op))
    return json::Object{{"op", "store"},
                        {"src", num.values.lookup(store.getValue())},
                        {"buf", num.buffers.lookup(store.getBuf())},
                        {"base", static_cast<int64_t>(store.getBase())},
                        {"stride", static_cast<int64_t>(store.getStride())}};
  if (auto matvec = dyn_cast<tau::MatVecOp>(op)) {
    int64_t x = num.values.lookup(matvec.getX());
    return json::Object{{"op", "matvec"},
                        {"dst", num.define(matvec.getResult())},
                        {"x", x},
                        {"buf", num.buffers.lookup(matvec.getBuf())},
                        {"base", static_cast<int64_t>(matvec.getBase())},
                        {"stride", static_cast<int64_t>(matvec.getStride())},
                        {"n", static_cast<int64_t>(matvec.getN())}};
  }
  if (auto affine = dyn_cast<tau::AffineOp>(op)) {
    int64_t x = num.values.lookup(affine.getX());
    int64_t bias = num.values.lookup(affine.getBias());
    return json::Object{{"op", "affine"},
                        {"dst", num.define(affine.getResult())},
                        {"x", x},
                        {"bias", bias},
                        {"buf", num.buffers.lookup(affine.getBuf())},
                        {"base", static_cast<int64_t>(affine.getBase())},
                        {"stride", static_cast<int64_t>(affine.getStride())},
                        {"n", static_cast<int64_t>(affine.getN())}};
  }
  if (auto constant = dyn_cast<tau::ConstOp>(op))
    return json::Object{{"op", "const"},
                        {"dst", num.define(constant.getResult())},
                        {"values", json::Array(constant.getValues())}};
  if (auto select = dyn_cast<tau::SelectOp>(op)) {
    int64_t m = num.values.lookup(select.getM());
    int64_t a = num.values.lookup(select.getA());
    int64_t b = num.values.lookup(select.getB());
    return json::Object{{"op", "sel"},
                        {"dst", num.define(select.getResult())},
                        {"m", m},
                        {"a", a},
                        {"b", b}};
  }
  if (tau::isBinaryKernelOp(op)) {
    int64_t a = num.values.lookup(op.getOperand(0));
    int64_t b = num.values.lookup(op.getOperand(1));
    return json::Object{{"op", "bin"},
                        {"fn", tau::kernelName(op)},
                        {"dst", num.define(op.getResult(0))},
                        {"a", a},
                        {"b", b}};
  }
  if (tau::isUnaryKernelOp(op)) {
    int64_t a = num.values.lookup(op.getOperand(0));
    json::Object object{{"op", "un"},
                        {"fn", tau::kernelName(op)},
                        {"dst", num.define(op.getResult(0))},
                        {"a", a}};
    if (auto k = op.getAttrOfType<IntegerAttr>("k"))
      object["k"] = k.getInt();
    if (auto table = op.getAttrOfType<DenseI64ArrayAttr>("table"))
      object["table"] = json::Array(table.asArrayRef());
    return std::move(object);
  }
  return createStringError("cannot emit operation '" +
                           op.getName().getStringRef() + "'");
}

} // namespace

Expected<json::Value> tau::emitKernel(func::FuncOp func) {
  Numbering num;
  json::Array sizes;
  for (BlockArgument arg : func.getArguments()) {
    auto buf = dyn_cast<tau::BufType>(arg.getType());
    if (!buf)
      return createStringError("every argument must be a !tau.buf");
    num.buffers[arg] = static_cast<int64_t>(sizes.size());
    sizes.push_back(static_cast<int64_t>(buf.getSize()));
  }

  json::Array body;
  for (Operation &op : func.getBody().front()) {
    if (isa<func::ReturnOp>(op))
      continue;
    if (auto loop = dyn_cast<tau::ForOp>(op)) {
      json::Array inner;
      for (Operation &nested : loop.getBody().front()) {
        if (isa<tau::ForOp>(nested))
          return createStringError("tau.for must not be nested");
        Expected<json::Value> stmt = emitStmt(nested, num);
        if (!stmt)
          return stmt.takeError();
        inner.push_back(std::move(*stmt));
      }
      body.push_back(json::Object{{"op", "loop"},
                                  {"n", static_cast<int64_t>(loop.getN())},
                                  {"body", std::move(inner)}});
      continue;
    }
    Expected<json::Value> stmt = emitStmt(op, num);
    if (!stmt)
      return stmt.takeError();
    body.push_back(std::move(*stmt));
  }
  return json::Object{{"buffers", std::move(sizes)},
                      {"body", std::move(body)}};
}
