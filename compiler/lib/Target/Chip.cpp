#include "tau/Target/Target.h"

#include "mlir/IR/Builders.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/MemoryBuffer.h"

#include <algorithm>

using namespace llvm;
using namespace mlir;

tau::Chip tau::Chip::standard() {
  Chip chip;
  chip.kinds = {"mxm", "sxm", "mem", "mem", "vxm",
                "mem", "mem", "sxm", "mxm"};
  return chip;
}

int tau::Chip::delayAt(int pos) const {
  const std::string &kind = kinds[pos];
  if (kind == "mem")
    return memDelay;
  if (kind == "vxm")
    return vxmDelay;
  if (kind == "sxm")
    return sxmDelay;
  return mxmDelay;
}

int tau::Chip::maxDelay() const {
  return std::max({memDelay, vxmDelay, sxmDelay, mxmDelay});
}

json::Value tau::Chip::toJSON() const {
  return json::Object{
      {"kinds", json::Array(kinds)}, {"streams", streams},
      {"mxmWeights", mxmWeights},
      {"memDelay", memDelay},        {"vxmDelay", vxmDelay},
      {"sxmDelay", sxmDelay},        {"mxmDelay", mxmDelay},
  };
}

Expected<tau::Chip> tau::Chip::fromJSON(const json::Value &value) {
  const json::Object *object = value.getAsObject();
  if (!object)
    return createStringError("chip: expected an object");
  const json::Array *kinds = object->getArray("kinds");
  if (!kinds)
    return createStringError("chip: missing 'kinds'");

  Chip chip;
  for (const json::Value &kind : *kinds) {
    std::optional<StringRef> name = kind.getAsString();
    if (!name || (*name != "mem" && *name != "vxm" && *name != "sxm" &&
                  *name != "mxm"))
      return createStringError("chip: bad slice kind");
    chip.kinds.push_back(name->str());
  }
  auto field = [&](StringRef key, int &out) -> Error {
    std::optional<int64_t> number = object->getInteger(key);
    if (!number || *number < 0)
      return createStringError("chip: missing or negative '" + key + "'");
    out = static_cast<int>(*number);
    return Error::success();
  };
  if (Error e = field("streams", chip.streams))
    return std::move(e);
  if (Error e = field("memDelay", chip.memDelay))
    return std::move(e);
  if (Error e = field("vxmDelay", chip.vxmDelay))
    return std::move(e);
  if (Error e = field("sxmDelay", chip.sxmDelay))
    return std::move(e);
  if (Error e = field("mxmDelay", chip.mxmDelay))
    return std::move(e);
  if (object->get("mxmWeights"))
    if (Error e = field("mxmWeights", chip.mxmWeights))
      return std::move(e);
  return chip;
}

Expected<tau::Chip> tau::Chip::fromFile(StringRef path) {
  auto buffer = MemoryBuffer::getFile(path);
  if (!buffer)
    return createStringError("cannot read " + path);
  Expected<json::Value> parsed = json::parse((*buffer)->getBuffer());
  if (!parsed)
    return parsed.takeError();
  return fromJSON(*parsed);
}

// The chip is recorded on a placed function as JSON text, so that the later
// passes work from the same description that `tau-place` used.
static constexpr const char *chipAttr = "tau.chip";

void tau::setChip(func::FuncOp func, const Chip &chip) {
  std::string text = formatv("{0}", chip.toJSON()).str();
  func->setAttr(chipAttr, StringAttr::get(func.getContext(), text));
}

Expected<tau::Chip> tau::chipOf(func::FuncOp func) {
  auto attr = func->getAttrOfType<StringAttr>(chipAttr);
  if (!attr)
    return createStringError("the function has not been placed: run tau-place");
  Expected<json::Value> parsed = json::parse(attr.getValue());
  if (!parsed)
    return parsed.takeError();
  return Chip::fromJSON(*parsed);
}

bool tau::isInstr(Operation &op) {
  return op.getName().getStringRef().starts_with("tau.i.");
}

StringRef tau::instrName(Operation &op) {
  return op.getName().getStringRef().drop_front(strlen("tau.i."));
}

int64_t tau::intAttr(Operation &op, StringRef name) {
  return op.getAttrOfType<IntegerAttr>(name).getInt();
}

std::optional<int64_t> tau::optIntAttr(Operation &op, StringRef name) {
  if (auto attr = op.getAttrOfType<IntegerAttr>(name))
    return attr.getInt();
  return std::nullopt;
}

void tau::setIntAttr(Operation &op, StringRef name, int64_t value) {
  op.setAttr(name, Builder(op.getContext()).getI64IntegerAttr(value));
}

Value tau::streamResult(Operation &op) {
  StringRef name = instrName(op);
  if (name == "read" || name == "un" || name == "bin" || name == "emit" ||
      name == "const" || name == "sel")
    return op.getResult(0);
  return Value();
}

StringRef tau::kernelName(Operation &op) {
  return op.getName().getStringRef().drop_front(strlen("tau."));
}

bool tau::isRearrangement(StringRef name) {
  return name == "shift" || name == "rotate" || name == "reverse" ||
         name == "broadcast" || name == "permute";
}

bool tau::isUnaryKernelOp(Operation &op) {
  if (!op.getName().getStringRef().starts_with("tau.") || isInstr(op))
    return false;
  StringRef name = kernelName(op);
  return name == "relu" || name == "requant" || name == "neg" ||
         name == "abs" || name == "shl" || name == "addi" || name == "muli" ||
         isRearrangement(name);
}

bool tau::isBinaryKernelOp(Operation &op) {
  if (!op.getName().getStringRef().starts_with("tau.") || isInstr(op))
    return false;
  StringRef name = kernelName(op);
  return name == "add" || name == "sub" || name == "mul" || name == "max" ||
         name == "min" || name == "and" || name == "or" || name == "xor" ||
         name == "lt";
}
