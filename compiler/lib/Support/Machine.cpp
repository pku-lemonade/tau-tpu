#include "tau/Machine.h"

#include "mlir/IR/Builders.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/MemoryBuffer.h"

#include <algorithm>

using namespace llvm;
using namespace mlir;

tau::Machine tau::Machine::standard() {
  Machine machine;
  machine.kinds = {"mxm", "sxm", "mem", "mem", "mem", "mem", "vxm",
                   "mem", "mem", "mem", "mem", "sxm", "mxm"};
  return machine;
}

int tau::Machine::delayAt(int pos) const {
  const std::string &kind = kinds[pos];
  if (kind == "mem")
    return memDelay;
  if (kind == "vxm")
    return vxmDelay;
  if (kind == "sxm")
    return sxmDelay;
  return mxmDelay;
}

int tau::Machine::delayOf(int pos, StringRef name) const {
  auto found = delays.find(name);
  return found != delays.end() ? found->getValue() : delayAt(pos);
}

int tau::Machine::maxDelay() const {
  int longest = std::max({memDelay, vxmDelay, sxmDelay, mxmDelay});
  for (const auto &entry : delays)
    longest = std::max(longest, entry.getValue());
  return longest;
}

json::Value tau::Machine::toJSON() const {
  json::Object object{
      {"kinds", json::Array(kinds)}, {"streams", streams},
      {"lanes", lanes},              {"bankSize", bankSize},
      {"memDelay", memDelay},        {"vxmDelay", vxmDelay},
      {"sxmDelay", sxmDelay},        {"mxmDelay", mxmDelay},
  };
  // Left out when empty, as Formats 3 allows, so that a machine without
  // delays of its own is written as before.
  if (!delays.empty()) {
    json::Object own;
    // The key is copied: the object outlives this machine.
    for (const auto &entry : delays)
      own[entry.getKey().str()] = entry.getValue();
    object["delays"] = std::move(own);
  }
  return object;
}

Expected<tau::Machine> tau::Machine::fromJSON(const json::Value &value) {
  const json::Object *object = value.getAsObject();
  if (!object)
    return createStringError("machine: expected an object");
  const json::Array *kinds = object->getArray("kinds");
  if (!kinds)
    return createStringError("machine: missing 'kinds'");

  Machine machine;
  for (const json::Value &kind : *kinds) {
    std::optional<StringRef> name = kind.getAsString();
    if (!name || (*name != "mem" && *name != "vxm" && *name != "sxm" &&
                  *name != "mxm"))
      return createStringError("machine: bad slice kind");
    machine.kinds.push_back(name->str());
  }
  auto field = [&](StringRef key, int &out) -> Error {
    std::optional<int64_t> number = object->getInteger(key);
    if (!number || *number < 0)
      return createStringError("machine: missing or negative '" + key + "'");
    out = static_cast<int>(*number);
    return Error::success();
  };
  if (Error e = field("streams", machine.streams))
    return std::move(e);
  if (Error e = field("bankSize", machine.bankSize))
    return std::move(e);
  if (Error e = field("memDelay", machine.memDelay))
    return std::move(e);
  if (Error e = field("vxmDelay", machine.vxmDelay))
    return std::move(e);
  if (Error e = field("sxmDelay", machine.sxmDelay))
    return std::move(e);
  if (Error e = field("mxmDelay", machine.mxmDelay))
    return std::move(e);
  if (Error e = field("lanes", machine.lanes))
    return std::move(e);
  if (const json::Object *own = object->getObject("delays"))
    for (const auto &[name, value] : *own) {
      std::optional<int64_t> number = value.getAsInteger();
      if (!number || *number < 0)
        return createStringError("machine: bad delay for '" + StringRef(name) +
                                 "'");
      machine.delays[name] = static_cast<int>(*number);
    }
  return machine;
}

Expected<tau::Machine> tau::Machine::fromFile(StringRef path) {
  auto buffer = MemoryBuffer::getFile(path);
  if (!buffer)
    return createStringError("cannot read " + path);
  Expected<json::Value> parsed = json::parse((*buffer)->getBuffer());
  if (!parsed)
    return parsed.takeError();
  return fromJSON(*parsed);
}

// The machine is recorded on a placed function as JSON text, so that the later
// passes work from the same description that `tau-place` used.
static constexpr const char *machineAttr = "tau.machine";

void tau::setMachine(func::FuncOp func, const Machine &machine) {
  std::string text = formatv("{0}", machine.toJSON()).str();
  func->setAttr(machineAttr, StringAttr::get(func.getContext(), text));
}

Expected<tau::Machine> tau::machineOf(func::FuncOp func) {
  auto attr = func->getAttrOfType<StringAttr>(machineAttr);
  if (!attr)
    return createStringError("the function has not been placed: run tau-place");
  Expected<json::Value> parsed = json::parse(attr.getValue());
  if (!parsed)
    return parsed.takeError();
  return Machine::fromJSON(*parsed);
}
