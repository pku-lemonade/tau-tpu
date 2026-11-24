# File formats

The compiler and the Lean tools exchange four kinds of JSON file. The reader
is `Tau/Sim/Json.lean`; the writer is `compiler/lib/Target/`.

## Kernel file

What the user wrote, before any compiler pass.

```json
{
  "buffers": [1, 1, 2, 1],
  "body": [
    {"op": "load", "dst": 0, "buf": 0, "base": 0, "stride": 0},
    {"op": "matvec", "dst": 1, "x": 0, "buf": 2, "base": 0, "stride": 0, "n": 2},
    {"op": "bin", "fn": "add", "dst": 3, "a": 1, "b": 2},
    {"op": "un", "fn": "requant", "k": 0, "dst": 4, "a": 3},
    {"op": "store", "src": 4, "buf": 3, "base": 0, "stride": 0},
    {"op": "loop", "n": 4, "body": []}
  ]
}
```

- `buffers` gives the number of words in each buffer. Buffers are numbered
  from 0 in this order.
- `dst`, `src`, `a`, `b` and `x` are value numbers.
- A position is `base + stride * i`, where `i` is the iteration of the
  enclosing loop, or 0 outside a loop.
- One-word functions (`un`): `relu`, `neg`, `abs`, `reverse` take nothing;
  `requant`, `shl`, `addi`, `muli`, `shift`, `rotate`, `broadcast` take an
  integer `k`; `permute` takes a list `table`.
- Two-word functions (`bin`): `add`, `sub`, `mul`, `max`, `min`, `and`, `or`,
  `xor`, `lt`.
- Other statements: `{"op": "const", "dst": 0, "values": [1, 2]}`,
  `{"op": "sel", "dst": 3, "m": 0, "a": 1, "b": 2}`, and `affine`, which is
  `matvec` with one more field, `bias`.
- A `loop` body holds statements only. Loops do not nest.

## Placed file

The output of `tau-place`: the chip, the memory map, and the instructions in
the order they must take effect. There are no cycles and no streams yet.

```json
{
  "config": {"kinds": ["mxm", "sxm", "mem", "mem", "vxm", "mem", "mem", "sxm", "mxm"],
             "streams": 8, "memDelay": 1, "vxmDelay": 1, "sxmDelay": 1, "mxmDelay": 2},
  "memSizes": [0, 0, 2, 1, 0, 2, 1, 0, 0],
  "map": [{"slice": 2, "base": 0, "size": 1}],
  "instructions": [
    {"op": "read", "slice": 2, "addr": 0, "dst": 0},
    {"op": "load", "slice": 0, "src": 0},
    {"op": "read", "slice": 5, "addr": 0, "dst": 1},
    {"op": "mac", "slice": 0, "j": 0, "src": 1},
    {"op": "emit", "slice": 0, "dst": 2},
    {"op": "bin", "fn": "add", "slice": 4, "a": 2, "b": 3, "dst": 4},
    {"op": "write", "slice": 6, "addr": 0, "src": 4}
  ]
}
```

- `dst`, `src`, `a`, `b` and `m` are numbers naming words in transit. Each
  is produced once and used by one instruction.
- Instructions (`op`): `read`, `write`, `un`, `bin`, `const`, `sel`, `load`,
  `seed`, `mac`, `install`, `macw`, `emit`.
- The fields are those of `Tau.PInstr` in `Tau/Check/Stages.lean`.

## Compiled file

The chip, the memory map and the timed program. `tauc` writes two of these:
`scheduled.json` after `tau-schedule`, in which every word has a stream to
itself and `streams` is raised to make room, and `compiled.json` after
`tau-route`.

```json
{
  "config": {
    "kinds": ["mxm", "sxm", "mem", "mem", "vxm", "mem", "mem", "sxm", "mxm"],
    "streams": 8, "mxmWeights": 8,
    "memDelay": 1, "vxmDelay": 1, "sxmDelay": 1, "mxmDelay": 2
  },
  "memSizes": [0, 0, 2, 1, 0, 2, 1, 0, 0],
  "map": [{"slice": 2, "base": 0, "size": 1}],
  "cycles": 25,
  "program": [
    {"slice": 5, "time": 0, "op": "read", "addr": 0, "dst": {"dir": "west", "id": 0},
     "repeats": 1, "gap": 0, "stride": 1},
    {"slice": 0, "time": 6, "op": "load", "src": {"dir": "west", "id": 0}}
  ]
}
```

- `config` is the chip. A file containing only this object is a chip file,
  accepted by `tauc --chip`.
- `memSizes` gives the number of words of memory at each position.
- `map` places each buffer, in buffer order: its slice, first address and
  length. Memory words outside every buffer are scratch space.
- `cycles` is how long to run.
- `mxmWeights` is the number of columns a matrix slice can store. It may be
  left out, and is then 8.
- Instructions (`op`): `read`, `write`, `un`, `bin`, `const`, `sel`, `load`,
  `seed`, `mac`, `install`, `macw`, `emit`. Their fields are those of
  `Tau.Instr` in `Tau/Isa/Instr.lean`.
- An entry with `repeats`, `gap` and `stride` is issued `repeats` more times
  after the first, with `gap` idle cycles between issues, and with its `addr`
  (for `read` and `write`) or `j` (for `mac`, `install` and `macw`) growing by
  `stride` each time. All three may be left out, and are then 0. `tauc` merges
  runs of instructions into such entries when it writes the file.

## What `tauc` writes

| File | Kind | After |
|---|---|---|
| `kernel.json` | kernel | parsing |
| `simplified.json` | kernel | `tau-simplify` |
| `unrolled.json` | kernel | `tau-unroll` |
| `placed.json` | placed | `tau-place` |
| `scheduled.json` | compiled | `tau-schedule` |
| `compiled.json` | compiled | `tau-route` |

`tau-check kernel.json <file>` and `tau-sim <file> buffers.json` accept any of
them and tell the kind from the fields present.

## Buffers file

Buffer contents for a run, as signed integers.

```json
{
  "lanes": 2,
  "buffers": [
    [[3, -2]],
    [[1, 3], [2, 4]]
  ]
}
```

Each buffer is a list of words, and each word is a list of `lanes` integers.
`tau-sim` prints its result in the same format.
