#!/usr/bin/env bash
# Compile every example and check every stage of the compiler on it.
#
# For each examples/<name>/kernel.mlir, tauc writes one file per pass:
#
#   simplified  unrolled  placed  scheduled  compiled
#
# For each of those files:
#   1. tau-check must accept it against the kernel as written.
#   2. tau-sim must give the same buffers for it as for the kernel.
#   3. A damaged copy of it must be rejected by tau-check.
#
# In addition, unrolled.json must be the kernel that the Lean model of
# tau-unroll gives for simplified.json (`tau-check --unroll`).
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
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

STAGES="simplified unrolled placed scheduled compiled"

# Damage a stage file so that it no longer computes the kernel.
damage() {
  python3 - "$1" "$2" <<'PY'
import json, sys
stage = json.load(open(sys.argv[1]))
if "body" in stage:
    # A kernel: drop its last store.
    def drop(items):
        for i in range(len(items) - 1, -1, -1):
            if items[i]["op"] == "store":
                del items[i]
                return True
            if items[i]["op"] == "loop" and drop(items[i]["body"]):
                return True
        return False
    drop(stage["body"])
elif "instructions" in stage:
    # A placed program: drop its last write.
    for i in range(len(stage["instructions"]) - 1, -1, -1):
        if stage["instructions"][i]["op"] == "write":
            del stage["instructions"][i]
            break
else:
    # A timed program: issue its last instruction one cycle late.
    stage["program"][-1]["time"] += 1
    stage["cycles"] += 1
json.dump(stage, open(sys.argv[2], "w"))
PY
}

status=0
for kernel in examples/*/kernel.mlir; do
  dir=$(dirname "$kernel")
  name=$(basename "$dir")
  out="$OUT/$name"
  failed=""

  # An example may name the chip it is for in a file called `chip`.
  chip=()
  if [ -f "$dir/chip" ]; then
    chip=(--chip "$(cat "$dir/chip")")
  fi

  if ! "$TAUC" "$kernel" -o "$out" "${chip[@]}"; then
    echo "FAIL $name: tauc failed"
    status=1
    continue
  fi
  "$SIM" "$out/kernel.json" "$dir/buffers.json" > "$out/reference.out"

  # An example may keep a copy of the compiler's output in `stages/`, for
  # readers who have not built the compiler. It must be up to date. Refresh
  # it with UPDATE_STAGES=1.
  if [ -d "$dir/stages" ]; then
    if [ "${UPDATE_STAGES:-}" = 1 ]; then
      cp "$out"/kernel.json "$out"/simplified.json "$out"/unrolled.json \
         "$out"/placed.json "$out"/scheduled.json "$out"/compiled.json "$dir/stages/"
    elif ! diff -rq "$dir/stages" "$out" --exclude='*.out' --exclude=verdict \
         --exclude=damaged.json > /dev/null; then
      echo "FAIL $name: $dir/stages is out of date (rerun with UPDATE_STAGES=1)"
      status=1
      continue
    fi
  fi

  if ! "$CHECK" --unroll "$out/simplified.json" "$out/unrolled.json" > /dev/null; then
    failed="unrolled: not the kernel the Lean model of tau-unroll gives"
  fi

  for stage in $STAGES; do
    [ -z "$failed" ] || break
    file="$out/$stage.json"
    if ! "$CHECK" "$out/kernel.json" "$file" > "$out/verdict"; then
      failed="$stage: $(cat "$out/verdict")"
      break
    fi
    "$SIM" "$file" "$dir/buffers.json" > "$out/$stage.out"
    if ! cmp -s "$out/$stage.out" "$out/reference.out"; then
      failed="$stage: different buffers from the kernel"
      break
    fi
    damage "$file" "$out/damaged.json"
    if "$CHECK" "$out/kernel.json" "$out/damaged.json" > /dev/null; then
      failed="$stage: a damaged copy was accepted"
      break
    fi
  done

  if [ -n "$failed" ]; then
    echo "FAIL $name: $failed"
    status=1
  else
    cycles=$(python3 -c "import json; print(json.load(open('$out/compiled.json'))['cycles'])")
    echo "ok   $name ($cycles cycles, 5 stages checked)"
  fi
done
exit $status
