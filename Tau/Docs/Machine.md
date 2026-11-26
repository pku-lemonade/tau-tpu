# The machine

| | |
|---|---|
| Describes | The tau-tpu machine: its components, its slices and streams, what one cycle does, the timing rule, the instructions, the traps, how a program is laid out in time, and the numbers a machine is loaded with. |
| Does not describe | What a user writes ([`Programs.md`](Programs.md)), how a program gets from there to the machine ([`Compiler.md`](Compiler.md)), or the files the tools exchange ([`README.md`](README.md) 5). |
| Specified in | `Tau/Data/`, `Tau/Blocks/`, `Tau/Isa/`, `Tau/SliceLevel/`, `Tau/CellLevel/` |
| Tables tested by | `tests/TauTest/Docs.lean`, with the rows in `course/Specs/Tables.lean` |

This doc describes the machine in words and tables, the way an architect
hands it to someone who has to specify it. The Lean files named above are
that specification; README 1 says how the two are kept together.

The machine is described twice. Section 3, the *slice-level machine*, treats
a slice as one box that takes an instruction and gives a result some cycles
later. Section 4, the *cell-level machine*, builds each box from the
components of section 2. The two must behave the same.

## 1. Conventions

The machine has one clock. Cycles are numbered from 0.

A *component* has a state, takes one input in every cycle and gives one
output in every cycle. The output during cycle `t` may depend on the input of
cycle `t` and on the state at the start of cycle `t`. The state at the start
of cycle `t + 1` is decided during cycle `t`.

A table lists, for each cycle, the input and the output.

A *lane* is a 32-bit value, read as a signed integer. Arithmetic on lanes
wraps on overflow. A *word* is a fixed number of lanes side by side. The
number of lanes is the same everywhere on a machine.

## 2. Components

### 2.1 Shift register

A shift register of depth `n` has `n` slots. In every cycle the input enters
the first slot, every stored value moves one slot along, and the value that
was in the last slot is the output. At cycle 0 every slot holds the reset
value.

So the output is the input of `n` cycles earlier.

Depth 2, reset value 0:

| Cycle | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| Input | 10 | 11 | 12 | 13 | 14 |
| Output | 0 | 0 | 10 | 11 | 12 |

Depth 1, reset value 0:

| Cycle | 0 | 1 | 2 |
|---|---|---|---|
| Input | 5 | 6 | 7 |
| Output | 0 | 5 | 6 |

### 2.2 Accumulator

An accumulator holds a running total. In every cycle it is given one command.

| Command | Effect on the total |
|---|---|
| hold | none |
| add `x` | `x` is added |
| clear | it goes back to its starting value |
| load `x` | it is replaced by `x` |

The output during a cycle is the total at the start of that cycle, before the
command takes effect.

Starting value 0:

| Cycle | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| Command | add 1 | add 2 | add 3 | hold | clear | add 5 | hold |
| Output | 0 | 1 | 3 | 6 | 6 | 0 | 5 |

### 2.3 Multiply-accumulate cell

A multiply-accumulate cell (MAC) is an accumulator with a multiplier in front
of it. Its commands carry a pair of values, and the cell adds their product.

Starting value 0:

| Cycle | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| Command | add (1, 4) | add (2, 5) | add (3, 6) | hold |
| Output | 0 | 4 | 14 | 32 |

After three cycles the output is the dot product of (1, 2, 3) and (4, 5, 6).

### 2.4 Pipeline

A pipeline of depth `d` computes a function `f` of its input and gives the
result `d` cycles later. Until the first result arrives it outputs the reset
value.

Depth 2, `f` doubles its input, reset value 0:

| Cycle | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| Input | 1 | 2 | 3 | 4 | 5 |
| Output | 0 | 0 | 2 | 4 | 6 |

### 2.5 Memory

A memory holds a fixed number of words, numbered from address 0. In every
cycle it is given one command.

| Command | Effect | Output |
|---|---|---|
| idle | none | nothing |
| read `a` | none | the word at address `a` |
| write `a` `x` | the word at `a` becomes `x` | nothing |

A read answers in the same cycle. A write is visible from the next cycle on.

Two words, starting as 10 and 11:

| Cycle | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| Command | write 1 7 | read 1 | read 0 | idle |
| Output | nothing | 7 | 10 | nothing |

### 2.6 Sequencer

A sequencer holds a program: a list of items, each with the cycle on which it
is due. In every cycle it outputs the items due on that cycle. It has no
input.

Program: "read" at 1, "add" at 3, "write" at 3.

| Cycle | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| Output | none | read | none | add, write |

### 2.7 Repeater

A repeater is a sequencer whose entries can repeat. An entry gives:

| Field | Meaning |
|---|---|
| time | the cycle of the first issue |
| repeats | the number of further issues after the first |
| gap | the number of idle cycles between two issues |
| first | the item of the first issue |
| next | how the item changes from one issue to the next |

In every cycle the repeater outputs the items issued on that cycle.

One entry: time 2, repeats 2, gap 1, first item 5, next adds 1.

| Cycle | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| Output | none | none | 5 | none | 6 | none | 7 | none |

A repeater is built from three registers per entry: the number of issues
left, the number of cycles until the next issue, and the item the next issue
will carry.

### 2.8 Systolic array

A systolic array of `n` cells multiplies a matrix by a vector `x` that it
holds, one cell per element of `x`. In every cycle each cell is given one
coefficient. Cell `j` takes the partial sum stored after cell `j - 1` (zero
for cell 0), adds its coefficient times `x[j]`, and stores the result. The
output is the partial sum stored after the last cell.

To multiply the matrix `A` by `x`, feed the coefficient `A[i][j]` to cell `j`
at cycle `i + j`. The product of row `i` with `x` comes out at cycle `i + n`.

`x` is (10, 100) and `A` is [[1, 2], [3, 4]]:

| Cycle | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| Coefficient at cell 0 | 1 | 3 | 0 | 0 |
| Coefficient at cell 1 | 0 | 2 | 4 | 0 |
| Output | 0 | 0 | 210 | 430 |

## 3. The slice-level machine

### 3.1 Slices

A machine is a row of *slices*, numbered from position 0 in the west to the
last position in the east. Each slice is of one of four kinds.

| Kind | Name | What it does |
|---|---|---|
| memory | `mem` | stores words |
| vector | `vxm` | arithmetic on words, lane by lane |
| rearrangement | `sxm` | moves the lanes of a word around |
| matrix | `mxm` | multiply-accumulate, for matrix times vector |

A machine is described by the kind of slice at each position, the number of
streams in each direction, the number of columns a matrix slice can store,
and one delay for each kind of slice. `chips/tau9.json` describes a machine
of nine slices: matrix, rearrangement, two memories, vector, two memories,
rearrangement, matrix.

### 3.2 Streams

Words travel between slices on *streams*. A stream has a direction, east or
west, and a number. Each stream has one slot at every position, and a slot
holds one word or nothing.

In every cycle, every word on a stream moves one position in the stream's
direction. A word that moves past the end of the row is gone. All slots are
empty at cycle 0.

A slice reads from, and places results on, the slots at its own position.

```
── east ──▶  [0] ──▶ [1] ──▶ [2] ──▶ [3] ──▶ [4] ──▶ [5] ──▶ [6] ──▶ [7] ──▶ [8]
             mxm     sxm     mem     mem     vxm     mem     mem     sxm     mxm
◀─ west ──   [0] ◀── [1] ◀── [2] ◀── [3] ◀── [4] ◀── [5] ◀── [6] ◀── [7] ◀── [8]
```

### 3.3 One cycle

In every cycle each slice executes at most one instruction.

1. The slice reads its operands from the stream slots at its position and
   computes a result.
2. The result enters the slice's pipe. A result stays in the pipe for the
   delay of the slice's kind and then comes out.
3. Every stream moves one position. The results that came out of the pipes
   are placed on their streams, each at its slice's position.

### 3.4 The timing rule

A result computed by the slice at position `p` on cycle `t` can be read by
the slice at position `q` on cycle

    t + delay + 1 + |q - p|

and on no other cycle, where `delay` is the delay of the kind of the slice at
`p`. The stream must run from `p` towards `q`.

Three slices, memory, vector, memory, each with delay 1. The memory at
position 0 reads a word on cycle 0 for a stream going east:

| Cycle | Where the word is |
|---|---|
| 0 | read at slice 0; enters the pipe |
| 1 | leaves the pipe |
| 2 | on the stream at position 0 |
| 3 | on the stream at position 1 |
| 4 | on the stream at position 2 |

The slice at position 2 can use it on cycle 0 + 1 + 1 + 2 = 4.

```
cycle   0:mem               1:vxm               2:mem
  0     read ─▶ pipe
  1     leaves pipe
  2     stream[0] ────────▶
  3                         stream[1] ────────▶
  4                                             stream[2] ─▶ read
```

### 3.5 Instructions

An instruction names its operands and its result by stream.

| Kind | Instruction | Effect |
|---|---|---|
| memory | read `addr` to `dst` | the word at `addr` is the result |
| memory | write `src` at `addr` | the word on `src` is stored at `addr` |
| vector, rearrangement | `op` of `src` to `dst` | a one-word operation |
| vector | `op` of `a` and `b` to `dst` | a two-word operation |
| vector | constant to `dst` | a word with given lanes is the result |
| vector | select by `m` from `a` and `b` to `dst` | lane by lane, `a` where `m` is not zero and `b` elsewhere |
| matrix | load `src` | the word on `src` becomes the vector operand |
| matrix | mac `j` with `src` | lane `j` of the vector operand, times the word on `src`, is added to the accumulator |
| matrix | seed `src` | the accumulator is replaced by the word on `src` |
| matrix | install `j` from `src` | the word on `src` becomes stored column `j` |
| matrix | macw `j` | as mac, with stored column `j` in place of a stream |
| matrix | emit to `dst` | the accumulator is the result, and is cleared |

A matrix slice keeps a vector operand, an accumulator and a number of stored
columns. "Times" in mac means: every lane of the word is multiplied by the
one lane `j` of the vector operand.

### 3.6 Operations

One-word operations of the vector slice: relu (negative lanes become zero),
requantize by `k` (divide by 2 to the `k`, rounding down, then clamp to -128
.. 127), negate, absolute value, shift bits left by `k`, add a constant,
multiply by a constant.

One-word operations of the rearrangement slice: shift lanes by `k`, rotate
lanes by `k`, reverse, broadcast lane `j`, permute by a table.

Two-word operations of the vector slice: add, subtract, multiply, maximum,
minimum, and, or, exclusive or, less-than (1 or 0 in each lane).

### 3.7 Traps

A program that asks for something the machine cannot do makes it *trap*:
it stops, and reports what went wrong, at which slice and on which cycle.
The machine never guesses and never waits.

| Trap | Cause |
|---|---|
| empty read | an instruction read a stream slot that held nothing |
| bad track | an instruction named a stream that does not exist |
| bad address | a memory address or a stored column was out of range |
| wrong slice | an instruction was sent to a slice of the wrong kind |
| two instructions | two instructions were due at one slice on one cycle |
| no operand | a matrix slice was told to multiply before it was given a vector |
| no slice | the program names a slice the machine does not have |

### 3.8 A program for the machine

A program is a list of timed instructions. Each gives a slice, a cycle and an
instruction. There are no branches and no loops.

A timed instruction may repeat, as an entry of a repeater does (2.7): it
gives a number of further issues, a gap, and a stride. From one issue to the
next the address of a memory instruction, or the column of a matrix
instruction, grows by the stride.

To run a program, the memories are loaded with their starting contents, the
machine runs for a given number of cycles, and the result is the contents of
the memories at the end.

### 3.9 What a slice issues

A slice *issues* a word on the cycle on which it runs an instruction that
has a result, or one that writes a word to memory. The word is the result,
or the word written. A matrix slice issues nothing when it loads, seeds,
installs or multiplies; it issues its accumulator when it emits.

The three slices of 3.4 again. The memory at position 0 reads address 0 on
cycle 0 to a stream going east, the vector slice applies relu on cycle 3,
and the memory at position 2 writes the result at address 0 on cycle 6:

| Cycle | Slice | Issues |
|---|---|---|
| 0 | 0 | the word `a` that was at address 0 |
| 3 | 1 | relu of `a` |
| 6 | 2 | relu of `a`, written at address 0 |

A word is issued when its instruction runs, not when it reaches a stream:
the relu is issued on cycle 3 and is on its stream from cycle 5.

### 3.10 The image

A machine is not loaded with a list of instructions. Each slice is loaded with
numbers, and reads its own entries out of them. The numbers for all the
slices are the *image* of the program.

The numbers of one slice are the count of its entries and then the entries,
one after another. An entry does not say which slice it is for. It is

    time, repeats, gap, stride, opcode, operands

A stream is one number, and so is a signed integer:

| Stream | Number | | Integer | Number |
|---|---|---|---|---|
| 0 going east | 0 | | 0 | 0 |
| 0 going west | 1 | | 1 | 2 |
| 3 going east | 6 | | -1 | 1 |
| 3 going west | 7 | | 5 | 10 |
| | | | -5 | 9 |

| Opcode | Instruction | Operands |
|---|---|---|
| 0 | read | address, result stream |
| 1 | write | source stream, address |
| 2 | one-word operation | source stream, result stream, the operation |
| 3 | two-word operation | the operation, stream `a`, stream `b`, result stream |
| 4 | load | stream |
| 5 | mac | column, stream |
| 6 | emit | result stream |
| 7 | constant | result stream, how many lanes, the lanes |
| 8 | select | streams `m`, `a`, `b`, result stream |
| 9 | seed | stream |
| 10 | install | column, stream |
| 11 | macw | column |

A one-word operation is its number in the order of 3.6, from 0 for relu to
11 for permute, and then what it takes: nothing, `k`, a signed constant, or a
table as its length and its items. A two-word operation is its number in the
order of 3.6, from 0 for add to 8 for less-than.

| Entry | Numbers |
|---|---|
| on cycle 2, read address 0 to stream 0 going east | 2, 0, 0, 0, 0, 0, 0 |
| the same, 3 more times, 3 idle cycles apart, the address growing by 1 | 2, 3, 3, 1, 0, 0, 0 |
| on cycle 9, write stream 0 going west at address 4 | 9, 0, 0, 0, 1, 1, 4 |
| on cycle 6, relu of stream 0 going east to stream 0 going west | 6, 0, 0, 0, 2, 0, 1, 0 |
| on cycle 7, add 5 to every lane of stream 1 going east, to stream 1 going east | 7, 0, 0, 0, 2, 2, 2, 5, 10 |
| on cycle 4, the constant with lanes 3 and -4 to stream 2 going west | 4, 0, 0, 0, 7, 5, 2, 6, 7 |

## 4. The cell-level machine

Section 3 treats a slice as one box with a delay. Inside, a slice is built
from the components of section 2.

| Part of a slice | Component |
|---|---|
| issuing the slice's instructions on their cycles | repeater (2.7) |
| the pipe that holds results for the delay | shift register (2.1) |
| the stored words of a memory slice | memory (2.5) |
| the accumulator of a matrix slice | multiply-accumulate cells (2.3), one per lane |
| the stored columns of a matrix slice | a second, small memory (2.5) |

```
repeater (2.7) ──▶ [ slice: mem (2.5) / vxm / sxm / mxm (mac 2.3 + mem 2.5) ]
                         ▲                                       │
                         │                                       ▼
                   streams (in)                     shift register (2.1) ──▶ streams (out)
```

A machine built this way behaves exactly as section 3 says.
