# JSON formats

| | |
|---|---|
| Describes | The JSON formats that the frontend, the compiler and the Lean tools exchange: source/kernel, placed, compiled, image, buffers and timeline, and which tool writes which. |
| Does not describe | What the contents mean: a statement and a pin ([`Programs.md`](Programs.md)), an instruction and the numbers of an image ([`Machine.md`](Machine.md)), an IR ([`Compiler.md`](Compiler.md)). |
| Specified in | `spec/Tau/Tools/Json.lean` |
| Tables tested by | none; `scripts/check-examples.sh` reads every kind of file on every example |

The reader, `spec/Tau/Tools/Json.lean`, is the specification. The writers are
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
  "buffers": [1, 4, 2, 1],
  "body": [
    {"op": "load", "ty": "i8", "dst": 0, "buf": 0, "base": 0, "stride": 0},
    {"op": "matvec", "dst": 1, "x": 0, "buf": 2, "base": 0, "stride": 0, "n": 2},
    {"op": "load", "ty": "i32", "dst": 2, "buf": 1, "base": 0, "stride": 0},
    {"op": "bin", "fn": "add", "ty": "i32", "dst": 3, "a": 1, "b": 2},
    {"op": "un", "fn": "requant", "ty": "i32", "k": 0, "dst": 4, "a": 3},
    {"op": "store", "ty": "i8", "src": 4, "buf": 3, "base": 0, "stride": 0},
    {"op": "loop", "n": 4, "body": [
      {"op": "un", "fn": "relu", "ty": "i8", "dst": 6, "a": 5, "at": 6, "every": 4}
    ]},
    {"op": "call", "args": [0, 3], "at": 40, "body": [
      {"op": "load", "ty": "i8", "dst": 0, "buf": 0, "base": 0, "stride": 0}
    ]}
  ]
}
```

- `buffers` gives the number of words in each buffer. Buffers are numbered
  from 0 in this order. Buffer 1 above holds one value of type `i32`, which
  is four words.
- `dst`, `src`, `a`, `b` and `x` are value numbers.
- `ty` is the type of a statement (Programs 2): `i8`, `i16` or `i32`.
- A position is `base + stride * i`, where `i` is the iteration of the
  enclosing loop, or 0 outside a loop. It counts values of the statement's
  type (Programs 1).
- One-value functions (`un`): `relu`, `neg`, `abs`, `reverse` take nothing;
  `requant`, `shl`, `addi`, `muli`, `shift`, `rotate`, `broadcast` take an
  integer `k`; `permute` takes a list `table`; `widen` takes a type `to`.
- Two-value functions (`bin`): `add`, `sub`, `mul`, `max`, `min`, `and`, `or`,
  `xor`, `lt`.
- Other statements: `{"op": "const", "ty": "i8", "dst": 0, "values": [1, 2]}`,
  `{"op": "sel", "ty": "i8", "dst": 3, "m": 0, "a": 1, "b": 2}`.
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
in the order they must take effect. There are no cycles and no streams yet,
and no scratch space: `memSizes` covers the buffers and nothing else.

```json
{
  "config": {"kinds": ["mxm", "sxm", "mem", "mem", "mem", "mem", "vxm",
                       "mem", "mem", "mem", "mem", "sxm", "mxm"],
             "streams": 16, "lanes": 8, "bankSize": 64,
             "memDelay": 1, "vxmDelay": 1, "sxmDelay": 1, "mxmDelay": 2},
  "memSizes": [0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 1, 0, 0],
  "map": [{"parts": [{"slice": 2, "base": 0}], "size": 1},
          {"parts": [{"slice": 7, "base": 0}, {"slice": 8, "base": 0},
                     {"slice": 9, "base": 0}, {"slice": 10, "base": 0}], "size": 4},
          {"parts": [{"slice": 4, "base": 0}], "size": 2},
          {"parts": [{"slice": 5, "base": 0}], "size": 1}],
  "instructions": [
    {"op": "read", "slice": 2, "addr": 0, "dst": 0},
    {"op": "read", "slice": 4, "addr": 0, "dst": 1},
    {"op": "install", "slice": 0, "j": 0, "srcs": [1]},
    {"op": "read", "slice": 4, "addr": 1, "dst": 2},
    {"op": "install", "slice": 0, "j": 1, "srcs": [2]},
    {"op": "product", "slice": 0, "n": 2, "src": 0, "dst": [3, 4, 5, 6]},
    {"op": "read", "slice": 7, "addr": 0, "dst": 7},
    {"op": "read", "slice": 8, "addr": 0, "dst": 8},
    {"op": "read", "slice": 9, "addr": 0, "dst": 9},
    {"op": "read", "slice": 10, "addr": 0, "dst": 10},
    {"op": "bin", "fn": "add", "ty": "i32", "slice": 6,
     "a": [3, 4, 5, 6], "b": [7, 8, 9, 10], "dst": [11, 12, 13, 14]},
    {"op": "un", "fn": "requant", "ty": "i32", "k": 0, "slice": 6,
     "src": [11, 12, 13, 14], "dst": [15]},
    {"op": "write", "slice": 5, "addr": 0, "src": 15}
  ]
}
```

This is `examples/nn/linear` without its relu. Buffer 1, one value of type
`i32`, has a part in each of four memory slices.

- A number names a word in transit. Each is produced once, and any number
  of the instructions after it may use it.
- `dst` and `src` of a `read`, a `write` and the `src` of a `product` are
  one word. Every other `dst`, `src`, `a`, `b` and `m`, and `srcs`, is a
  list of words: those of one value, the low word first (Compiler 4).
- An instruction with `pin` must be issued on that cycle. `tau-place` puts
  the pin of a kernel statement on the instructions that issue its words:
  the `read`s of a load, the `write`s of a store, the `product` of a matrix
  product.
- Instructions (`op`): `read`, `write`, `un`, `bin`, `const`, `sel`,
  `install`, `product`.
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
    "kinds": ["mxm", "sxm", "mem", "mem", "mem", "mem", "vxm",
              "mem", "mem", "mem", "mem", "sxm", "mxm"],
    "streams": 16, "lanes": 8, "bankSize": 64,
    "memDelay": 1, "vxmDelay": 1, "sxmDelay": 1, "mxmDelay": 2
  },
  "memSizes": [0, 0, 1, 0, 2, 1, 0, 1, 1, 1, 1, 0, 0],
  "map": [{"parts": [{"slice": 2, "base": 0}], "size": 1}],
  "cycles": 25,
  "program": [
    {"slice": 4, "time": 0, "op": "read", "addr": 0, "dst": {"dir": "west", "id": 0},
     "repeats": 1, "gap": 0, "stride": 1},
    {"slice": 0, "time": 6, "op": "install", "j": 0, "g": 1,
     "src": {"dir": "west", "id": 0}, "repeats": 1, "gap": 0, "stride": 1},
    {"slice": 0, "time": 8, "op": "product", "n": 2,
     "src": {"dir": "west", "id": 0}, "dst": {"dir": "east", "id": 0}},
    {"slice": 6, "time": 17, "op": "bin", "fn": "add", "ty": "i32",
     "a": {"dir": "east", "id": 0}, "b": {"dir": "west", "id": 0},
     "dst": {"dir": "east", "id": 0}}
  ]
}
```

- `config` is the shape of the machine (Machine 3.1). A file containing only
  this object is a machine file, such as `machines/tau13.json`, accepted by
  `tauc --machine`.
- `memSizes` gives the number of words of memory at each position.
- `map` places each buffer, in buffer order: its parts, each a slice and a
  first address, and its length (Compiler 3). Memory words outside every
  buffer are scratch space.
- `cycles` is how long to run.
- `lanes` is the number of lanes of a word (Machine 1), and so the number of
  installed words of a matrix slice.
- `bankSize` is the number of words in the lower bank of a memory slice
  (Machine 3.11).
- `delays` gives instructions and operations a delay of their own, in place
  of their kind's, as an object such as `{"mul": 3, "read": 2}`. A key is the
  `fn` of a `un` or `bin` instruction, or the `op` of any other. It may be
  left out, and is then empty.
- Instructions (`op`): `read`, `write`, `un`, `bin`, `const`, `sel`,
  `install`, `product`. Their fields are those of `Tau.Instr` in
  `spec/Tau/Isa/Instr.lean`. A stream is the first of the streams of its
  value (Machine 3.5): the `add` above takes streams 0 to 3 going east and
  0 to 3 going west.
- An entry with `repeats`, `gap` and `stride` is issued `repeats` more times
  after the first, with `gap` idle cycles between issues, and with its `addr`
  (for `read` and `write`) or `j` (for `install`) growing by `stride` each
  time. All three may be left out, and are then 0. `tau-fold`
  makes such entries; the files before it have none.

## 4. Image

A compiled file with the program as numbers: `image` in place of `program`,
with one list of numbers for each slice of the machine. It is what the
machine would be loaded with.

```json
{
  "config": {"kinds": ["mxm", "sxm", "mem", "mem", "mem", "mem", "vxm",
                       "mem", "mem", "mem", "mem", "sxm", "mxm"],
             "streams": 16, "lanes": 8, "bankSize": 64,
             "memDelay": 1, "vxmDelay": 1, "sxmDelay": 1, "mxmDelay": 2},
  "memSizes": [0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  "map": [{"parts": [{"slice": 2, "base": 0}], "size": 4},
          {"parts": [{"slice": 3, "base": 0}], "size": 4}],
  "cycles": 15,
  "image": [
    [0],
    [0],
    [1, 0, 3, 0, 1, 0, 0, 0],
    [1, 11, 3, 0, 1, 1, 1, 0],
    [0], [0],
    [1, 6, 3, 0, 0, 2, 0, 0, 1, 0],
    [0], [0], [0], [0], [0], [0]
  ]
}
```

This is `examples/paced`. Slice 2 has one entry: from cycle 0, three more
times, with no idle cycle between, the address growing by 1; opcode 0, `read`,
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
    {"type": "i8", "values": [[3, -2]]},
    {"type": "i32", "values": [[100000, -20]]},
    {"type": "i8", "values": [[1, 2], [3, 4]]}
  ]
}
```

Each buffer has a type and a list of values of that type, and each value is
a list of `lanes` integers, its elements (Machine 1). A value of `w` words is
`w` words of the buffer (Programs 1). A compiled program runs on such values
if its machine has at least as many lanes.
`tau-sim` prints its result in the same format, each buffer with the type
the file gave it. A buffer the file leaves out starts as zeros and is
printed as values of type `i8`, so a file that fills a program's own buffers
serves every stage, scratch buffers included.

## 7. Timeline

What `tau-sim --timeline` and the frontend's `--timeline` print: the events
of a run, as a list.

```json
[
  {"time": 6, "word": [1, 0]},
  {"time": 9, "word": [1, 0], "buf": 1, "pos": 0}
]
```

An event is one word, each lane as a signed integer of 8 bits; a value of
several words makes one event for each (Programs 5). An event with `buf` and
`pos` is a store to that word of that buffer. For a
source program, a kernel or a placed program the events are those of the
pinned operations. For a compiled program or an image they are every word a
slice issues.
