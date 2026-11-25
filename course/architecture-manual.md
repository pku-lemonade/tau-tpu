# Architecture manual

This is course material. It describes the tau-tpu chip in words and tables,
the way an architect would hand it to someone who has to specify it, and the
course has you write the specification from it.

It is not the specification, and it is not the documentation of this
repository. The specification is the Lean code under `Tau/`, and where the
two disagree the Lean code is right. For a description of the repository,
read `docs/overview.md`. Like every manual, this one leaves things unsaid;
where it is silent, the Lean code has decided. The course asks you to find
those places.

Every table here is also a test. `course/Specs/Tables.lean` holds the same
rows, and `tests/TauTest/Manual.lean` runs them on the definitions in `Tau/`.

## 1. Conventions

The chip has one clock. Cycles are numbered from 0.

A *component* has a state, takes one input in every cycle and gives one
output in every cycle. The output during cycle `t` may depend on the input of
cycle `t` and on the state at the start of cycle `t`. The state at the start
of cycle `t + 1` is decided during cycle `t`.

A table lists, for each cycle, the input and the output.

A *lane* is a 32-bit value, read as a signed integer. Arithmetic on lanes
wraps on overflow. A *word* is a fixed number of lanes side by side. The
number of lanes is the same everywhere on a chip.

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

## 3. The machine

### 3.1 The chip

A chip is a row of *slices*, numbered from position 0 in the west to the last
position in the east. Each slice is of one of four kinds.

| Kind | Name | What it does |
|---|---|---|
| memory | `mem` | stores words |
| vector | `vxm` | arithmetic on words, lane by lane |
| rearrangement | `sxm` | moves the lanes of a word around |
| matrix | `mxm` | multiply-accumulate, for matrix times vector |

A chip is described by the kind of slice at each position, the number of
streams in each direction, the number of columns a matrix slice can store,
and one delay for each kind of slice. `chips/tau9.json` is a chip of nine
slices: matrix, rearrangement, two memories, vector, two memories,
rearrangement, matrix.

### 3.2 Streams

Words travel between slices on *streams*. A stream has a direction, east or
west, and a number. Each stream has one slot at every position, and a slot
holds one word or nothing.

In every cycle, every word on a stream moves one position in the stream's
direction. A word that moves past the end of the row is gone. All slots are
empty at cycle 0.

A slice reads from, and places results on, the slots at its own position.

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

A program that asks for something the chip cannot do makes the chip *trap*:
it stops, and reports what went wrong, at which slice and on which cycle.
The chip never guesses and never waits.

| Trap | Cause |
|---|---|
| empty read | an instruction read a stream slot that held nothing |
| bad track | an instruction named a stream that does not exist |
| bad address | a memory address or a stored column was out of range |
| wrong slice | an instruction was sent to a slice of the wrong kind |
| two instructions | two instructions were due at one slice on one cycle |
| no operand | a matrix slice was told to multiply before it was given a vector |
| no slice | the program names a slice the chip does not have |

### 3.8 Programs

A program is a list of timed instructions. Each gives a slice, a cycle and an
instruction. There are no branches and no loops.

A timed instruction may repeat, as an entry of a repeater does (2.7): it
gives a number of further issues, a gap, and a stride. From one issue to the
next the address of a memory instruction, or the column of a matrix
instruction, grows by the stride.

To run a program, the memories are loaded with their starting contents, the
chip runs for a given number of cycles, and the result is the contents of
the memories at the end.

## 4. Inside a slice

Section 3 treats a slice as one box with a delay. Inside, a slice is built
from the components of section 2.

| Part of a slice | Component |
|---|---|
| issuing the slice's instructions on their cycles | repeater (2.7) |
| the pipe that holds results for the delay | shift register (2.1) |
| the stored words of a memory slice | memory (2.5) |
| the accumulator of a matrix slice | multiply-accumulate cells (2.3), one per lane |
| the stored columns of a matrix slice | a second, small memory (2.5) |

A chip built this way behaves exactly as section 3 says.
