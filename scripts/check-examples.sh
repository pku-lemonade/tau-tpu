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

  if ! "$TAUC" "$kernel" -o "$out"; then
    echo "FAIL $name: tauc failed"
    status=1
    continue
  fi
  "$SIM" "$out/kernel.json" "$dir/buffers.json" > "$out/reference.out"

  for stage in $STAGES; do
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
