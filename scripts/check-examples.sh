#!/usr/bin/env bash
# Compile every example and check every pass of the compiler on it.
#
# An example is examples/<name>/kernel.mlir, or examples/<name>/kernel.py,
# which the Python frontend records as a kernel.mlir first. For each, tauc
# writes the program as written and one file per pass:
#
#   source  kernel  simplified  unrolled  placed  scheduled  routed  sliced
#   compiled  image
#
# For each pass:
#   1. tau-check must accept its output against its input, the file before.
#      That covers the buffers and the pins.
#   2. tau-sim must give the same buffers for its output as for the source.
#   3. tau-check must reject a damaged copy of its output.
#
# In addition:
#   - tau-check must accept image.json against source.json. This is the
#     check of the whole compiler, the one the end-to-end theorem is about.
#   - unrolled.json must be the kernel that the Lean model of tau-unroll
#     gives for simplified.json (`tau-check --unroll`).
#   - image.json must be the image that the Lean encoding gives for
#     compiled.json (`tau-check --encode`).
#   - If the source has pins, a copy of compiled.json with every instruction
#     one cycle late must be rejected against source.json: it computes the
#     same buffers and misses every pin.
#
# For an example written in Python:
#   - the source file the frontend writes (traced.json) must be the one tauc
#     writes from the frontend's MLIR (source.json);
#   - the program run in Python on real numbers must end with the buffers,
#     and issue the pinned words, that tau-sim gives for source.json.
#
# `examples/linear/stages/` holds a copy of those files, so that the course
# can be followed without building the compiler. The script fails if the copy
# is stale; UPDATE_STAGES=1 refreshes it.
#
# Build first: `lake build tau-sim tau-check` and `cmake --build compiler/build`.
set -euo pipefail
cd "$(dirname "$0")/.."

TAUC=compiler/build/bin/tauc
SIM=.lake/build/bin/tau-sim
CHECK=.lake/build/bin/tau-check
FRONTEND="env PYTHONPATH=frontend python3 -m tau"
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

STAGES="kernel simplified unrolled placed scheduled routed sliced compiled image"
FILES="source $STAGES"

# Damage a stage file so that it no longer does what the source does.
damage() {
  python3 - "$1" "$2" <<'PY'
import json, sys
stage = json.load(open(sys.argv[1]))
if "body" in stage:
    # A source program or a kernel: drop its last store.
    def drop(items):
        for i in range(len(items) - 1, -1, -1):
            if items[i]["op"] == "store":
                del items[i]
                return True
            if items[i]["op"] in ("loop", "call") and drop(items[i]["body"]):
                return True
        return False
    drop(stage["body"])
elif "instructions" in stage:
    # A placed program: drop its last write.
    for i in range(len(stage["instructions"]) - 1, -1, -1):
        if stage["instructions"][i]["op"] == "write":
            del stage["instructions"][i]
            break
elif "program" in stage:
    # A timed program: issue its last instruction one cycle late.
    stage["program"][-1]["time"] += 1
    stage["cycles"] += 1
else:
    # An image: the same, for the first entry of the last slice that has one.
    # A slice's list is its number of entries, then for each its cycle first.
    for numbers in reversed(stage["image"]):
        if numbers[0] > 0:
            numbers[1] += 1
            break
    stage["cycles"] += 1
json.dump(stage, open(sys.argv[2], "w"))
PY
}

# A copy of a compiled file in which everything happens one cycle late.
late() {
  python3 - "$1" "$2" <<'PY'
import json, sys
stage = json.load(open(sys.argv[1]))
for entry in stage["program"]:
    entry["time"] += 1
stage["cycles"] += 1
json.dump(stage, open(sys.argv[2], "w"))
PY
}

# Whether two JSON files hold the same value. With `events`, both are lists
# and their order does not count.
same_json() {
  python3 - "$@" <<'PY'
import json, sys
a, b = (json.load(open(p)) for p in sys.argv[1:3])
if len(sys.argv) > 3:
    key = lambda e: json.dumps(e, sort_keys=True)
    a, b = sorted(a, key=key), sorted(b, key=key)
sys.exit(0 if a == b else 1)
PY
}

status=0
for dir in examples/*/; do
  dir=${dir%/}
  name=$(basename "$dir")
  out="$OUT/$name"
  failed=""
  mkdir -p "$out"

  if [ -f "$dir/kernel.py" ]; then
    if ! $FRONTEND "$dir/kernel.py" -o "$out"; then
      echo "FAIL $name: the frontend failed"
      status=1
      continue
    fi
    kernel="$out/kernel.mlir"
  elif [ -f "$dir/kernel.mlir" ]; then
    kernel="$dir/kernel.mlir"
  else
    continue
  fi

  # An example may name the machine it is for in a file called `chip`.
  chip=()
  if [ -f "$dir/chip" ]; then
    chip=(--chip "$(cat "$dir/chip")")
  fi

  if ! "$TAUC" "$kernel" -o "$out" "${chip[@]}"; then
    echo "FAIL $name: tauc failed"
    status=1
    continue
  fi
  "$SIM" "$out/source.json" "$dir/buffers.json" > "$out/reference.out"
  "$SIM" --timeline "$out/source.json" "$dir/buffers.json" > "$out/reference.events"

  # An example may keep a copy of the compiler's output in `stages/`, for
  # readers who have not built the compiler. It must be up to date. Refresh
  # it with UPDATE_STAGES=1.
  if [ -d "$dir/stages" ]; then
    if [ "${UPDATE_STAGES:-}" = 1 ]; then
      rm -f "$dir"/stages/*.json
      for file in $FILES; do cp "$out/$file.json" "$dir/stages/"; done
    else
      for file in $FILES; do
        if ! cmp -s "$out/$file.json" "$dir/stages/$file.json"; then
          failed="$dir/stages is out of date (rerun with UPDATE_STAGES=1)"
        fi
      done
    fi
  fi

  # The frontend against the compiler and against the Lean tools.
  if [ -z "$failed" ] && [ -f "$dir/kernel.py" ]; then
    $FRONTEND "$dir/kernel.py" --run "$dir/buffers.json" > "$out/python.out"
    $FRONTEND "$dir/kernel.py" --timeline "$dir/buffers.json" > "$out/python.events"
    if ! same_json "$out/traced.json" "$out/source.json"; then
      failed="frontend: its source file is not the one tauc writes"
    elif ! same_json "$out/python.out" "$out/reference.out"; then
      failed="frontend: run in Python, the program ends with other buffers"
    elif ! same_json "$out/python.events" "$out/reference.events" events; then
      failed="frontend: run in Python, the program issues other pinned words"
    fi
  fi

  if [ -z "$failed" ] &&
     ! "$CHECK" --unroll "$out/simplified.json" "$out/unrolled.json" > /dev/null; then
    failed="unrolled: not the kernel the Lean model of tau-unroll gives"
  fi
  if [ -z "$failed" ] &&
     ! "$CHECK" --encode "$out/compiled.json" "$out/image.json" > /dev/null; then
    failed="image: not the image the Lean encoding gives"
  fi

  before=source
  for stage in $STAGES; do
    [ -z "$failed" ] || break
    file="$out/$stage.json"
    if ! "$CHECK" "$out/$before.json" "$file" > "$out/verdict"; then
      failed="$stage: $(cat "$out/verdict")"
      break
    fi
    "$SIM" "$file" "$dir/buffers.json" > "$out/$stage.out"
    if ! cmp -s "$out/$stage.out" "$out/reference.out"; then
      failed="$stage: different buffers from the source"
      break
    fi
    damage "$file" "$out/damaged.json"
    if "$CHECK" "$out/$before.json" "$out/damaged.json" > /dev/null; then
      failed="$stage: a damaged copy was accepted"
      break
    fi
    before=$stage
  done

  if [ -z "$failed" ] &&
     ! "$CHECK" "$out/source.json" "$out/image.json" > "$out/verdict"; then
    failed="whole compiler: $(cat "$out/verdict")"
  fi

  # With pins in the source, being late is being wrong.
  pins=$(python3 -c "import json; print(len(json.load(open('$out/reference.events'))))")
  if [ -z "$failed" ] && [ "$pins" -gt 0 ]; then
    late "$out/compiled.json" "$out/late.json"
    if "$CHECK" "$out/source.json" "$out/late.json" > /dev/null; then
      failed="pins: a program that is one cycle late was accepted"
    fi
  fi

  if [ -n "$failed" ]; then
    echo "FAIL $name: $failed"
    status=1
  else
    cycles=$(python3 -c "import json; print(json.load(open('$out/compiled.json'))['cycles'])")
    note="9 passes checked"
    [ "$pins" -gt 0 ] && note="$note, $pins pinned words on time"
    [ -f "$dir/kernel.py" ] && note="$note, frontend agrees"
    echo "ok   $name ($cycles cycles, $note)"
  fi
done
exit $status
