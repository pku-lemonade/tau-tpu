//===- Emit.cpp - write placed and compiled files -------------------------===//
//
// Writes a function made of instructions in the JSON forms that the Lean
// tools read (docs/formats.md, Tau/Sim/Json.lean).
//
//===----------------------------------------------------------------------===//

#include "tau/Target/Target.h"

#include "llvm/ADT/DenseMap.h"

#include <algorithm>

using namespace llvm;
using namespace mlir;

namespace {

/// The parts of a placed or compiled file that describe the chip and its
/// memory.
Expected<json::Object> header(func::FuncOp func) {
  Expected<tau::Chip> chip = tau::chipOf(func);
  if (!chip)
    return chip.takeError();
  auto sizes = func->getAttrOfType<ArrayAttr>("tau.mem_sizes");
  auto map = func->getAttrOfType<ArrayAttr>("tau.map");
  if (!sizes || !map)
    return createStringError("the function has not been placed");

  json::Array memSizes;
  for (Attribute size : sizes)
    memSizes.push_back(cast<IntegerAttr>(size).getInt());
  json::Array placements;
  for (Attribute entry : map) {
    auto triple = cast<ArrayAttr>(entry);
    placements.push_back(
        json::Object{{"slice", cast<IntegerAttr>(triple[0]).getInt()},
                     {"base", cast<IntegerAttr>(triple[1]).getInt()},
                     {"size", cast<IntegerAttr>(triple[2]).getInt()}});
  }
  return json::Object{{"config", chip->toJSON()},
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
  for (StringRef key : {"addr", "k", "j"})
    if (std::optional<int64_t> value = tau::optIntAttr(op, key))
      body[key] = *value;
  return body;
}

/// Add the operands and the result of an instruction to `body`, each written
/// by `name`.
template <typename NameFn>
void connect(Operation &op, json::Object &body, NameFn name) {
  StringRef kind = tau::instrName(op);
  if (kind == "write" || kind == "un" || kind == "load")
    body["src"] = name(op.getOperand(0));
  if (kind == "mac")
    body["src"] = name(op.getOperand(1));
  if (kind == "bin") {
    body["a"] = name(op.getOperand(0));
    body["b"] = name(op.getOperand(1));
  }
  if (Value result = tau::streamResult(op))
    body["dst"] = name(result);
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
    if (Value result = streamResult(op))
      numbers[result] = static_cast<int64_t>(numbers.size());
    json::Object body = common(op);
    connect(op, body,
            [&](Value value) -> json::Value { return numbers.lookup(value); });
    instructions.push_back(std::move(body));
  }
  (*file)["instructions"] = std::move(instructions);
  return std::move(*file);
}

Expected<json::Value> tau::emitCompiled(func::FuncOp func, bool idealRouting) {
  Expected<json::Object> file = header(func);
  if (!file)
    return file.takeError();
  auto cycles = func->getAttrOfType<IntegerAttr>("tau.cycles");
  if (!cycles)
    return createStringError("the function has not been scheduled");

  // The stream of every travelling word.
  struct Track {
    bool east;
    int64_t id;
  };
  llvm::DenseMap<Value, Track> tracks;
  int64_t streamsNeeded = 0;
  int64_t fresh[2] = {0, 0};
  for (Operation &op : func.getBody().front()) {
    if (!isInstr(op))
      continue;
    Value result = streamResult(op);
    if (!result)
      continue;
    Track track{true, 0};
    if (idealRouting) {
      if (!result.use_empty())
        track.east = intAttr(*result.use_begin()->getOwner(), "slice") >=
                     intAttr(op, "slice");
      track.id = fresh[track.east]++;
    } else {
      auto east = op.getAttrOfType<BoolAttr>("east");
      std::optional<int64_t> stream = optIntAttr(op, "stream");
      if (!east || !stream)
        return createStringError("the function has not been routed");
      track = {east.getValue(), *stream};
    }
    streamsNeeded = std::max(streamsNeeded, track.id + 1);
    tracks[result] = track;
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
    connect(op, body, [&](Value value) -> json::Value {
      Track track = tracks.lookup(value);
      return json::Object{{"dir", track.east ? "east" : "west"},
                          {"id", track.id}};
    });
    timed.push_back({*time, std::move(body)});
  }
  std::stable_sort(timed.begin(), timed.end(),
                   [](const auto &x, const auto &y) { return x.first < y.first; });
  json::Array program;
  for (auto &entry : timed)
    program.push_back(std::move(entry.second));

  if (idealRouting) {
    json::Object *config = (*file)["config"].getAsObject();
    int64_t streams = config->getInteger("streams").value_or(0);
    (*config)["streams"] = std::max(streams, streamsNeeded);
  }
  (*file)["cycles"] = cycles.getInt();
  (*file)["program"] = std::move(program);
  return std::move(*file);
}
