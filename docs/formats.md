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
- One-word functions (`un`): `relu`, `requant`, `shift`, `rotate`. The last
  three take `k`.
- Two-word functions (`bin`): `add`, `sub`, `mul`, `max`, `min`.
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

- `dst`, `src`, `a` and `b` are numbers naming words in transit. Each is
  produced once and used once.
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
    "streams": 8,
    "memDelay": 1, "vxmDelay": 1, "sxmDelay": 1, "mxmDelay": 2
  },
  "memSizes": [0, 0, 2, 1, 0, 2, 1, 0, 0],
  "map": [{"slice": 2, "base": 0, "size": 1}],
  "cycles": 25,
  "program": [
    {"slice": 2, "time": 0, "op": "read", "addr": 0, "dst": {"dir": "west", "id": 0}},
    {"slice": 0, "time": 4, "op": "load", "src": {"dir": "west", "id": 0}}
  ]
}
```

- `config` is the chip. A file containing only this object is a chip file,
  accepted by `tauc --chip`.
- `memSizes` gives the number of words of memory at each position.
- `map` places each buffer, in buffer order: its slice, first address and
  length. Memory words outside every buffer are scratch space.
- `cycles` is how long to run.
- Instructions (`op`): `read`, `write`, `un`, `bin`, `load`, `mac`, `emit`.
  Their fields are those of `Tau.Instr` in `Tau/Isa/Instr.lean`.

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
