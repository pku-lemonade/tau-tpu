# JSON formats

| | |
|---|---|
| Describes | The JSON formats that the frontend, the compiler and the Lean tools exchange: source/kernel, placed, compiled, image, buffers and timeline, and which tool writes which. |
| Does not describe | What the contents mean: a statement and a pin ([`Programs.md`](Programs.md)), an instruction and the numbers of an image ([`Machine.md`](Machine.md)), an IR ([`Compiler.md`](Compiler.md)). |
| Specified in | `spec/Tau/Sim/Json.lean` |
| Tables tested by | none; `scripts/check-examples.sh` reads every kind of file on every example |

The reader, `spec/Tau/Sim/Json.lean`, is the specification. The writers are
`compiler/lib/Emit/` and, for source files, also `compiler/python/tau/`.
Each IR of a program (Compiler 2) has a file. The Lean tools tell the kind
of a file from the fields present.

## 1. Source and kernel

A program before it has slices: buffers, statements, loops and calls. With a
call in it the file is a *source* file (`Tau.Source`); with none it is a
*kernel* file (`Tau.Kernel`). A kernel is a call-free source program, so
`tau-check` accepts a call-free `source.json` as a `Source` (for example
`tau-check out/source.json out/image.json` on `examples/nn/linear`). `tau-inline`
turns the first into the second.

```json
{
  "buffers": [1, 1, 2, 1],
  "body": [
    {"op": "load", "dst": 0, "buf": 0, "base": 0, "stride": 0},
    {"op": "matvec", "dst": 1, "x": 0, "buf": 2, "base": 0, "stride": 0, "n": 2},
    {"op": "bin", "fn": "add", "dst": 3, "a": 1, "b": 2},
    {"op": "un", "fn": "requant", "k": 0, "dst": 4, "a": 3},
    {"op": "store", "src": 4, "buf": 3, "base": 0, "stride": 0},
    {"op": "loop", "n": 4, "body": [
      {"op": "un", "fn": "relu", "dst": 6, "a": 5, "at": 6, "every": 4}
    ]},
    {"op": "call", "args": [0, 3], "at": 40, "body": [
      {"op": "load", "dst": 0, "buf": 0, "base": 0, "stride": 0}
    ]}
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
- A statement with `at` is pinned (Programs 5). In a loop the cycle is
  `at + every * i`. `every` may be left out, and is then 0.
- A `call` (Programs 4) carries the called kernel's statements as its
  `body`, with value numbers and buffer numbers of their own: the kernel's
  buffer `j` is the caller's buffer `args[j]`. `at` is the origin.
- A program's scratch buffers, which the frontend's `tau.alloc` makes, come
  after the buffers the user fills.

## 2. Placed

The output of `tau-place`: the machine, the memory map, and the instructions
in the order they must take effect. There are no cycles and no streams yet.

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
- An instruction with `pin` must be issued on that cycle. `tau-place` puts
  the pin of a kernel statement on the instruction that issues its word: the
  `read` of a load, the `write` of a store, the `emit` of a matrix product.
- Instructions (`op`): `read`, `write`, `un`, `bin`, `const`, `sel`, `load`,
  `seed`, `mac`, `install`, `macw`, `emit`.
- The fields are those of `Tau.PInstr` in `spec/Tau/IR/Placed.lean`.

## 3. Compiled

The machine, the memory map and the timed program. `tauc` writes four of
these: `scheduled.json` after `tau-schedule`, in which every word has a
stream to itself and `streams` is raised to make room; `routed.json` after
`tau-route`; `sliced.json` after `tau-slice`, with the entries listed slice
by slice; and `compiled.json` after `tau-fold`.

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

- `config` is the shape of the machine (Machine 3.1). A file containing only
  this object is a machine file, such as `machines/tau9.json`, accepted by
  `tauc --machine`.
- `memSizes` gives the number of words of memory at each position.
- `map` places each buffer, in buffer order: its slice, first address and
  length. Memory words outside every buffer are scratch space.
- `cycles` is how long to run.
- `mxmWeights` is the number of columns a matrix slice can store. It may be
  left out, and is then 8.
- Instructions (`op`): `read`, `write`, `un`, `bin`, `const`, `sel`, `load`,
  `seed`, `mac`, `install`, `macw`, `emit`. Their fields are those of
  `Tau.Instr` in `spec/Tau/Isa/Instr.lean`.
- An entry with `repeats`, `gap` and `stride` is issued `repeats` more times
  after the first, with `gap` idle cycles between issues, and with its `addr`
  (for `read` and `write`) or `j` (for `mac`, `install` and `macw`) growing by
  `stride` each time. All three may be left out, and are then 0. `tau-fold`
  makes such entries; the files before it have none.

## 4. Image

A compiled file with the program as numbers: `image` in place of `program`,
with one list of numbers for each slice of the machine. It is what the
machine would be loaded with.

```json
{
  "config": {"kinds": ["mxm", "sxm", "mem", "mem", "vxm", "mem", "mem", "sxm", "mxm"],
             "streams": 8, "mxmWeights": 8,
             "memDelay": 1, "vxmDelay": 1, "sxmDelay": 1, "mxmDelay": 2},
  "memSizes": [0, 0, 4, 4, 0, 0, 0, 0, 0],
  "map": [{"slice": 2, "base": 0, "size": 4}, {"slice": 3, "base": 0, "size": 4}],
  "cycles": 22,
  "image": [
    [0],
    [0],
    [1, 2, 3, 3, 1, 0, 0, 0],
    [1, 9, 3, 3, 1, 1, 1, 0],
    [1, 6, 3, 3, 0, 2, 0, 1, 0],
    [0], [0], [0], [0]
  ]
}
```

This is `examples/paced`. Slice 2 has one entry: from cycle 2, three more
times, 3 idle cycles apart, the address growing by 1; opcode 0, `read`,
address 0, onto stream 0 going east.

The numbers are those of Machine 3.10: for each slice the count of its
entries and then each entry, as `time, repeats, gap, stride, opcode,
operands`. The tools read an image back with `Image.decode`
(`spec/Tau/Isa/Encode.lean`), and to them an image is the compiled program it
decodes to.

## 5. What the tools write

| File | Kind | After |
|---|---|---|
| `kernel.mlir`, `traced.json` | MLIR text, source | the frontend, `python3 -m tau kernel.py -o out` |
| `source.json` | source or kernel | parsing |
| `inlined.json` | kernel | `tau-inline` |
| `simplified.json` | kernel | `tau-simplify` |
| `unrolled.json` | kernel | `tau-unroll` |
| `placed.json` | placed | `tau-place` |
| `scheduled.json` | compiled | `tau-schedule` |
| `routed.json` | compiled | `tau-route` |
| `sliced.json` | compiled | `tau-slice` |
| `compiled.json` | compiled | `tau-fold` |
| `image.json` | image | `tau-encode` |

`traced.json` and `source.json` are the same program written by two
programs, the frontend and `tauc`; `scripts/check-examples.sh` fails if they
differ.

`tau-sim <file> buffers.json` runs any of them, and
`tau-sim --timeline <file> buffers.json` prints its events. `tau-check
<before> <after>` compares two of them: a pass's input with its output, or
`source.json` with `image.json`. Both tools tell the kind of a file from the
fields present.

## 6. Buffers

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
`tau-sim` prints its result in the same format. A buffer the file leaves out
starts as zeros, so a file that fills a program's own buffers serves every
stage, scratch buffers included.

## 7. Timeline

What `tau-sim --timeline` and the frontend's `--timeline` print: the events
of a run, as a list.

```json
[
  {"time": 6, "word": [1, 0]},
  {"time": 9, "word": [1, 0], "buf": 1, "pos": 0}
]
```

An event with `buf` and `pos` is a store to that word of that buffer. For a
source program, a kernel or a placed program the events are those of the
pinned operations. For a compiled program or an image they are every word a
slice issues.
