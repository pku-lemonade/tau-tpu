//===- Emit.cpp - write placed and compiled files -------------------------===//
//
// Writes a function made of instructions in the JSON forms that the Lean
// tools read (docs/formats.md, Tau/Sim/Json.lean).
//
//===----------------------------------------------------------------------===//

#include "tau/Target/Target.h"

#include "llvm/ADT/DenseMap.h"

#include <algorithm>
#include <map>

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
  for (StringRef key : {"table", "values"})
    if (auto array = op.getAttrOfType<DenseI64ArrayAttr>(key))
      body[key] = json::Array(array.asArrayRef());
  return body;
}

/// Add the operands and the result of an instruction to `body`, each written
/// by `name`.
template <typename NameFn>
void connect(Operation &op, json::Object &body, NameFn name) {
  StringRef kind = tau::instrName(op);
  if (kind == "write" || kind == "un" || kind == "load" || kind == "install")
    body["src"] = name(op.getOperand(0));
  if (kind == "mac" || kind == "seed")
    body["src"] = name(op.getOperand(1));
  if (kind == "bin") {
    body["a"] = name(op.getOperand(0));
    body["b"] = name(op.getOperand(1));
  }
  if (kind == "sel") {
    body["m"] = name(op.getOperand(0));
    body["a"] = name(op.getOperand(1));
    body["b"] = name(op.getOperand(2));
  }
  if (Value result = tau::streamResult(op))
    body["dst"] = name(result);
}

/// The field of an instruction that a repeat can step: the address of a
/// memory instruction or the column of a matrix instruction.
const char *steppedField(const json::Object &body) {
  StringRef op = body.getString("op").value_or("");
  if (op == "read" || op == "write")
    return "addr";
  if (op == "mac" || op == "install" || op == "macw")
    return "j";
  return nullptr;
}

/// Merge runs of instructions that one slice issues at a fixed spacing, and
/// that differ only by a fixed step in their address or column, into one
/// repeating entry each. `timed` holds (cycle, instruction) pairs.
std::vector<std::pair<int64_t, json::Object>>
compress(std::vector<std::pair<int64_t, json::Object>> timed) {
  // The instructions of each slice, in order of time.
  std::map<int64_t, std::vector<size_t>> bySlice;
  std::stable_sort(timed.begin(), timed.end(),
                   [](const auto &x, const auto &y) { return x.first < y.first; });
  for (size_t i = 0; i < timed.size(); ++i)
    bySlice[timed[i].second.getInteger("slice").value_or(0)].push_back(i);

  // An instruction with its time and stepped field taken out.
  auto shape = [](json::Object body) {
    if (const char *field = steppedField(body))
      body.erase(field);
    body.erase("time");
    return json::Value(std::move(body));
  };
  auto stepped = [](const json::Object &body) -> int64_t {
    const char *field = steppedField(body);
    return field ? body.getInteger(field).value_or(0) : 0;
  };

  std::vector<std::pair<int64_t, json::Object>> out;
  for (auto &entry : bySlice) {
    const std::vector<size_t> &order = entry.second;
    for (size_t i = 0; i < order.size();) {
      const json::Object &first = timed[order[i]].second;
      size_t end = i + 1;
      int64_t period = 0;
      int64_t stride = 0;
      if (end < order.size() &&
          shape(first) == shape(timed[order[end]].second)) {
        period = timed[order[end]].first - timed[order[i]].first;
        stride = stepped(timed[order[end]].second) - stepped(first);
        if (period >= 1 && stride >= 0) {
          ++end;
          while (end < order.size() &&
                 shape(first) == shape(timed[order[end]].second) &&
                 timed[order[end]].first - timed[order[end - 1]].first ==
                     period &&
                 stepped(timed[order[end]].second) -
                         stepped(timed[order[end - 1]].second) ==
                     stride)
            ++end;
        } else {
          end = i + 1;
        }
      }
      json::Object body = first;
      if (end - i > 1) {
        body["repeats"] = static_cast<int64_t>(end - i - 1);
        body["gap"] = period - 1;
        body["stride"] = stride;
      }
      out.push_back({timed[order[i]].first, std::move(body)});
      i = end;
    }
  }
  std::stable_sort(out.begin(), out.end(),
                   [](const auto &x, const auto &y) { return x.first < y.first; });
  return out;
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
  json::Array program;
  for (auto &entry : compress(std::move(timed)))
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
