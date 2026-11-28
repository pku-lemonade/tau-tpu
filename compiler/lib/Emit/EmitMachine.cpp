//===- EmitMachine.cpp - write placed, compiled and image files -----------===//
//
// Writes a function made of instructions, entries or images in the JSON
// formats that the Lean tools read (docs/Formats.md, spec/Tau/Tools/Json.lean).
// Each file says what is in the IR; the numbers of the image are worked out by
// `tau-encode` (lib/Passes/Encode.cpp).
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Emit.h"
#include "tau/Machine.h"
#include "tau/OpUtils.h"

#include "llvm/ADT/DenseMap.h"

#include <algorithm>
#include <map>

using namespace llvm;
using namespace mlir;

namespace {

/// The parts of a placed or compiled file that describe the machine and its
/// memory.
Expected<json::Object> header(func::FuncOp func) {
  Expected<tau::Machine> machine = tau::machineOf(func);
  if (!machine)
    return machine.takeError();
  auto sizes = func->getAttrOfType<ArrayAttr>("tau.mem_sizes");
  auto map = func->getAttrOfType<ArrayAttr>("tau.map");
  if (!sizes || !map)
    return createStringError("the function has not been placed");

  json::Array memSizes;
  for (Attribute size : sizes)
    memSizes.push_back(cast<IntegerAttr>(size).getInt());
  json::Array placements;
  for (Attribute entry : map) {
    // The size, then each part's slice and first address (`tau-place`).
    auto numbers = cast<ArrayAttr>(entry);
    json::Array parts;
    for (size_t i = 1; i + 1 < numbers.size(); i += 2)
      parts.push_back(
          json::Object{{"slice", cast<IntegerAttr>(numbers[i]).getInt()},
                       {"base", cast<IntegerAttr>(numbers[i + 1]).getInt()}});
    placements.push_back(
        json::Object{{"parts", std::move(parts)},
                     {"size", cast<IntegerAttr>(numbers[0]).getInt()}});
  }
  return json::Object{{"config", machine->toJSON()},
                      {"memSizes", std::move(memSizes)},
                      {"map", std::move(placements)}};
}

/// The fields of an instruction that do not depend on how its operands and
/// result are named.
json::Object common(Operation &op) {
  json::Object body{{"op", tau::instrName(op)},
                    {"slice", tau::intAttr(op, "slice")}};
  if (auto fn = op.getAttrOfType<StringAttr>("fn"))
    body["fn"] = fn.getValue();
  for (StringRef key : {"addr", "k", "j", "n"})
    if (std::optional<int64_t> value = tau::optIntAttr(op, key))
      body[key] = *value;
  for (StringRef key : {"table", "values"})
    if (auto array = op.getAttrOfType<DenseI64ArrayAttr>(key))
      body[key] = json::Array(array.asArrayRef());
  if (std::optional<int64_t> bits = tau::optIntAttr(op, "bits"))
    body["ty"] = tau::typeName(*bits);
  if (std::optional<int64_t> to = tau::optIntAttr(op, "to"))
    body["to"] = tau::typeName(*to);
  return body;
}

/// Add the operands and the result of an instruction to `body`, each word
/// written by `name`. A value of several words is written word by word if
/// `each`, and otherwise as its first word: on the machine its words are on
/// streams that follow one another. The words of an `install` are written
/// the same way, with how many there are.
template <typename NameFn>
void connect(Operation &op, json::Object &body, NameFn name, bool each) {
  StringRef kind = tau::instrName(op);
  auto value = [&](ArrayRef<Value> words) -> json::Value {
    if (!each)
      return name(words.front());
    json::Array names;
    for (Value word : words)
      names.push_back(name(word));
    return std::move(names);
  };
  std::vector<std::vector<Value>> values = tau::operandValues(op);
  if (kind == "write" || kind == "product")
    body["src"] = name(op.getOperand(0));
  if (kind == "un")
    body["src"] = value(values[0]);
  if (kind == "install") {
    if (each) {
      body["srcs"] = value(values[0]);
    } else {
      body["g"] = static_cast<int64_t>(values[0].size());
      body["src"] = name(values[0].front());
    }
  }
  if (kind == "bin") {
    body["a"] = value(values[0]);
    body["b"] = value(values[1]);
  }
  if (kind == "sel") {
    body["m"] = value(values[0]);
    body["a"] = value(values[1]);
    body["b"] = value(values[2]);
  }
  if (kind == "read") {
    body["dst"] = name(op.getResult(0));
  } else if (tau::streamResult(op)) {
    SmallVector<Value> results(op.result_begin(), op.result_end());
    body["dst"] = value(results);
  }
}

/// The slices of a function that `tau-slice` has run on. Empty before.
std::vector<tau::SliceOp> slicesOf(func::FuncOp func) {
  std::vector<tau::SliceOp> slices;
  for (tau::SliceOp slice : func.getBody().front().getOps<tau::SliceOp>())
    slices.push_back(slice);
  return slices;
}

/// "e3" -> {"dir": "east", "id": 3}.
json::Value streamJSON(StringRef name) {
  int64_t id = 0;
  name.drop_front().getAsInteger(10, id);
  return json::Object{{"dir", name.starts_with("e") ? "east" : "west"},
                      {"id", id}};
}

} // namespace

Expected<json::Value> tau::emitPlaced(func::FuncOp func) {
  Expected<json::Object> file = header(func);
  if (!file)
    return file.takeError();

  // Travelling words are numbered in the order they are produced.
  llvm::DenseMap<Value, int64_t> numbers;
  json::Array instructions;
  for (Operation &op : func.getBody().front()) {
    if (!isInstr(op))
      continue;
    if (streamResult(op))
      for (Value result : op.getResults())
        numbers[result] = static_cast<int64_t>(numbers.size());
    json::Object body = common(op);
    connect(
        op, body,
        [&](Value value) -> json::Value { return numbers.lookup(value); },
        /*each=*/true);
    if (std::optional<int64_t> pin = optIntAttr(op, "pin"))
      body["pin"] = *pin;
    instructions.push_back(std::move(body));
  }
  (*file)["instructions"] = std::move(instructions);
  return std::move(*file);
}

Expected<json::Value> tau::emitCompiled(func::FuncOp func) {
  Expected<json::Object> file = header(func);
  if (!file)
    return file.takeError();
  auto cycles = func->getAttrOfType<IntegerAttr>("tau.cycles");
  if (!cycles)
    return createStringError("the function has not been scheduled");
  (*file)["cycles"] = cycles.getInt();

  // After `tau-slice`: the entries, slice by slice.
  std::vector<tau::SliceOp> slices = slicesOf(func);
  if (!slices.empty()) {
    json::Array program;
    for (tau::SliceOp slice : slices)
      for (tau::EntryOp entry : slice.getBody().front().getOps<tau::EntryOp>()) {
        json::Object body{{"op", entry.getInstr()},
                          {"slice", static_cast<int64_t>(slice.getPosition())},
                          {"time", static_cast<int64_t>(entry.getTime())}};
        if (auto fn = entry.getFn())
          body["fn"] = *fn;
        for (StringRef key :
             {"addr", "k", "j", "g", "n", "repeats", "gap", "stride"})
          if (std::optional<int64_t> value = optIntAttr(*entry, key))
            body[key] = *value;
        if (std::optional<int64_t> bits = optIntAttr(*entry, "bits"))
          body["ty"] = typeName(*bits);
        if (std::optional<int64_t> to = optIntAttr(*entry, "to"))
          body["to"] = typeName(*to);
        for (StringRef key : {"table", "values"})
          if (auto array = entry->getAttrOfType<DenseI64ArrayAttr>(key))
            body[key] = json::Array(array.asArrayRef());
        for (StringRef key : {"src", "a", "b", "m", "dst"})
          if (auto name = entry->getAttrOfType<StringAttr>(key))
            body[key] = streamJSON(name.getValue());
        program.push_back(std::move(body));
      }
    (*file)["program"] = std::move(program);
    return std::move(*file);
  }

  // Before: the instructions, each with the stream of every word it uses,
  // as `tau-schedule` or `tau-route` gave it.
  struct Stream {
    bool east;
    int64_t id;
  };
  llvm::DenseMap<Value, Stream> streams;
  for (Operation &op : func.getBody().front()) {
    if (!isInstr(op))
      continue;
    if (!streamResult(op))
      continue;
    auto east = op.getAttrOfType<BoolAttr>("east");
    std::optional<int64_t> stream = optIntAttr(op, "stream");
    if (!east || !stream)
      return createStringError("the function has not been scheduled");
    // The words of a result are on streams that follow one another.
    for (Value result : op.getResults())
      streams[result] = Stream{
          east.getValue(),
          *stream + cast<OpResult>(result).getResultNumber()};
  }

  std::vector<std::pair<int64_t, json::Object>> timed;
  for (Operation &op : func.getBody().front()) {
    if (!isInstr(op))
      continue;
    std::optional<int64_t> time = optIntAttr(op, "time");
    if (!time)
      return createStringError("the function has not been scheduled");
    json::Object body = common(op);
    body["time"] = *time;
    connect(
        op, body,
        [&](Value value) -> json::Value {
          Stream on = streams.lookup(value);
          return json::Object{{"dir", on.east ? "east" : "west"},
                              {"id", on.id}};
        },
        /*each=*/false);
    timed.push_back({*time, std::move(body)});
  }
  std::stable_sort(timed.begin(), timed.end(),
                   [](const auto &x, const auto &y) { return x.first < y.first; });
  json::Array program;
  for (auto &entry : timed)
    program.push_back(std::move(entry.second));

  (*file)["program"] = std::move(program);
  return std::move(*file);
}

Expected<json::Value> tau::emitImage(func::FuncOp func) {
  Expected<json::Object> file = header(func);
  if (!file)
    return file.takeError();
  auto cycles = func->getAttrOfType<IntegerAttr>("tau.cycles");
  auto images = func.getBody().front().getOps<tau::ImageOp>();
  if (!cycles || images.empty())
    return createStringError("run tau-encode before writing the image");
  (*file)["cycles"] = cycles.getInt();

  json::Array image;
  for (tau::ImageOp slice : images)
    image.push_back(json::Array(slice.getNumbers()));
  (*file)["image"] = std::move(image);
  return std::move(*file);
}
