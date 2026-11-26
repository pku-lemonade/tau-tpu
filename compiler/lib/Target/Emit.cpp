//===- Emit.cpp - write placed, compiled and image files ------------------===//
//
// Writes a function made of instructions or entries in the JSON forms that
// the Lean tools read (Tau/Docs/Formats.md, Tau/Sim/Json.lean).
//
// The image is the last file: the entries of every slice as numbers. How an
// entry becomes numbers is specified in Tau/Isa/Encode.lean (`encode`), and
// this file follows it. The Lean tools read an image with `decode` from the
// same file, so a difference between the two shows up as a rejected image.
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
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

/// The slices of a function that `tau-slice` has run on. Empty before.
std::vector<tau::SliceOp> slicesOf(func::FuncOp func) {
  std::vector<tau::SliceOp> slices;
  for (tau::SliceOp slice : func.getBody().front().getOps<tau::SliceOp>())
    slices.push_back(slice);
  return slices;
}

/// "e3" -> {"dir": "east", "id": 3}.
json::Value trackJSON(StringRef name) {
  int64_t id = 0;
  name.drop_front().getAsInteger(10, id);
  return json::Object{{"dir", name.starts_with("e") ? "east" : "west"},
                      {"id", id}};
}

/// "e3" -> 6, "w3" -> 7: `Track.encode` in Tau/Isa/Encode.lean.
int64_t trackNumber(StringRef name) {
  int64_t id = 0;
  name.drop_front().getAsInteger(10, id);
  return 2 * id + (name.starts_with("e") ? 0 : 1);
}

/// `encodeInt` in Tau/Isa/Encode.lean.
int64_t intNumber(int64_t value) {
  return value >= 0 ? 2 * value : 2 * (-value) - 1;
}

/// One entry as numbers: `Timed.encode` in Tau/Isa/Encode.lean.
Error encodeEntry(tau::EntryOp entry, json::Array &out) {
  auto num = [&](StringRef key) {
    return tau::optIntAttr(*entry, key).value_or(0);
  };
  auto track = [&](StringRef key) {
    auto name = entry->getAttrOfType<StringAttr>(key);
    return name ? trackNumber(name.getValue()) : 0;
  };
  out.push_back(static_cast<int64_t>(entry.getTime()));
  out.push_back(num("repeats"));
  out.push_back(num("gap"));
  out.push_back(num("stride"));

  StringRef instr = entry.getInstr();
  if (instr == "read") {
    out.push_back(0);
    out.push_back(num("addr"));
    out.push_back(track("dst"));
  } else if (instr == "write") {
    out.push_back(1);
    out.push_back(track("src"));
    out.push_back(num("addr"));
  } else if (instr == "un") {
    out.push_back(2);
    out.push_back(track("src"));
    out.push_back(track("dst"));
    static const char *const plain[] = {"relu",  "requant", "neg",    "abs",
                                        "shl",   "addi",    "muli",   "shift",
                                        "rotate", "reverse", "broadcast",
                                        "permute"};
    StringRef fn = entry.getFn().value_or("");
    int64_t code = -1;
    for (int64_t c = 0; c < 12; ++c)
      if (fn == plain[c])
        code = c;
    if (code < 0)
      return createStringError("cannot encode the operation '" + fn + "'");
    out.push_back(code);
    if (fn == "addi" || fn == "muli") {
      out.push_back(intNumber(num("k")));
    } else if (fn == "permute") {
      ArrayRef<int64_t> table = *entry.getTable();
      out.push_back(static_cast<int64_t>(table.size()));
      for (int64_t item : table)
        out.push_back(item);
    } else if (fn != "relu" && fn != "neg" && fn != "abs" && fn != "reverse") {
      out.push_back(num("k"));
    }
  } else if (instr == "bin") {
    static const char *const fns[] = {"add", "sub", "mul", "max", "min",
                                      "and", "or",  "xor", "lt"};
    StringRef fn = entry.getFn().value_or("");
    int64_t code = -1;
    for (int64_t c = 0; c < 9; ++c)
      if (fn == fns[c])
        code = c;
    if (code < 0)
      return createStringError("cannot encode the operation '" + fn + "'");
    out.push_back(3);
    out.push_back(code);
    out.push_back(track("a"));
    out.push_back(track("b"));
    out.push_back(track("dst"));
  } else if (instr == "load") {
    out.push_back(4);
    out.push_back(track("src"));
  } else if (instr == "mac") {
    out.push_back(5);
    out.push_back(num("j"));
    out.push_back(track("src"));
  } else if (instr == "emit") {
    out.push_back(6);
    out.push_back(track("dst"));
  } else if (instr == "const") {
    out.push_back(7);
    out.push_back(track("dst"));
    ArrayRef<int64_t> values = *entry.getValues();
    out.push_back(static_cast<int64_t>(values.size()));
    for (int64_t value : values)
      out.push_back(intNumber(value));
  } else if (instr == "sel") {
    out.push_back(8);
    out.push_back(track("m"));
    out.push_back(track("a"));
    out.push_back(track("b"));
    out.push_back(track("dst"));
  } else if (instr == "seed") {
    out.push_back(9);
    out.push_back(track("src"));
  } else if (instr == "install") {
    out.push_back(10);
    out.push_back(num("j"));
    out.push_back(track("src"));
  } else if (instr == "macw") {
    out.push_back(11);
    out.push_back(num("j"));
  } else {
    return createStringError("cannot encode the instruction '" + instr + "'");
  }
  return Error::success();
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
    if (std::optional<int64_t> pin = optIntAttr(op, "pin"))
      body["pin"] = *pin;
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
        for (StringRef key : {"addr", "k", "j", "repeats", "gap", "stride"})
          if (std::optional<int64_t> value = optIntAttr(*entry, key))
            body[key] = *value;
        for (StringRef key : {"table", "values"})
          if (auto array = entry->getAttrOfType<DenseI64ArrayAttr>(key))
            body[key] = json::Array(array.asArrayRef());
        for (StringRef key : {"src", "a", "b", "m", "dst"})
          if (auto name = entry->getAttrOfType<StringAttr>(key))
            body[key] = trackJSON(name.getValue());
        program.push_back(std::move(body));
      }
    (*file)["program"] = std::move(program);
    return std::move(*file);
  }

  // Before: the instructions, each with the stream of every word it uses.
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
  (*file)["program"] = std::move(program);
  return std::move(*file);
}

Expected<json::Value> tau::emitImage(func::FuncOp func) {
  Expected<json::Object> file = header(func);
  if (!file)
    return file.takeError();
  auto cycles = func->getAttrOfType<IntegerAttr>("tau.cycles");
  std::vector<tau::SliceOp> slices = slicesOf(func);
  if (!cycles || slices.empty())
    return createStringError("run tau-slice before writing the image");
  (*file)["cycles"] = cycles.getInt();

  // One list per slice: how many entries, then each (`encodeSlice`).
  json::Array image;
  for (tau::SliceOp slice : slices) {
    json::Array numbers;
    int64_t count = 0;
    for (tau::EntryOp entry : slice.getBody().front().getOps<tau::EntryOp>()) {
      (void)entry;
      ++count;
    }
    numbers.push_back(count);
    for (tau::EntryOp entry : slice.getBody().front().getOps<tau::EntryOp>())
      if (Error e = encodeEntry(entry, numbers))
        return std::move(e);
    image.push_back(std::move(numbers));
  }
  (*file)["image"] = std::move(image);
  return std::move(*file);
}
