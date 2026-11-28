# The machine

| | |
|---|---|
| Describes | The tau-tpu machine: its blocks, its slices and streams, what one cycle does, the timing rule, the instructions, the traps, how a program is laid out in time, the numbers a machine is loaded with, and the two banks of a memory slice. |
| Does not describe | What a user writes ([`Programs.md`](Programs.md)), how a program gets from there to the machine ([`Compiler.md`](Compiler.md)), or the files the tools exchange ([`Formats.md`](Formats.md)). |
| Specified in | `spec/Tau/Isa/`, `spec/Tau/Blocks/`, `spec/Tau/Machine/` |
| Tables tested by | `course/tests/CourseTest/Docs.lean`, with the rows in `course/Specify/Support/Tables.lean` |

This doc describes the machine in words and tables, the way an architect
hands it to someone who has to specify it. The Lean files named above are
that specification; Docs/README 1 says how the two are kept together.

The machine is described twice. Section 3, the *slice-level machine*, treats
a slice as one box that takes an instruction and gives a result some cycles
later. Section 4, the *cell-level machine*, builds each box from the
blocks of section 2. The two must behave the same.

## 1. Conventions

The machine has one clock. Cycles are numbered from 0.

A *block*, or component, has a state, takes one input in every cycle and
gives one output in every cycle. The output during cycle `t` may depend on the
input of cycle `t` and on the state at the start of cycle `t`. The state at the start
of cycle `t + 1` is decided during cycle `t`.

A table lists, for each cycle, the input and the output.

A *lane* is 8 bits. A *word* is a fixed number of lanes side by side: it is
what one address of a memory holds and what one slot of a stream carries.
The number of lanes is the same everywhere on a machine, and is one of the
numbers a machine is described with (3.1).

A *value* is a row of signed integers, its *elements*, one for each lane.
Its *type* is the size of an element:

| Type | An element is | A value is |
|---|---|---|
| `i8` | 8 bits | 1 word |
| `i16` | 16 bits | 2 words |
| `i32` | 32 bits | 4 words |

Word `k` of a value holds byte `k` of every element, the low byte in word 0.
Arithmetic on elements wraps on overflow, at the size of the element.

With two lanes, the value of type `i16` with the elements 258 and -2 is the
words (2, -2) and (1, -1), each lane read as a signed integer.

## 2. Blocks

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
| vector | `vxm` | arithmetic on values, element by element |
| rearrangement | `sxm` | moves the elements of a value around |
| matrix | `mxm` | multiplies a matrix by a word |

A machine is described by the kind of slice at each position, the number of
streams in each direction, the number of lanes of a word, the number of
words in the lower bank of a memory slice (3.11), one delay
for each kind of slice, and a delay of its own for any instruction
or operation that takes a different number of cycles from the rest of its
kind. For example, a thirteen-slice machine has the row: matrix,
rearrangement, four memories, vector, four memories, rearrangement, matrix.

### 3.2 Streams

Words travel between slices on *streams*. A stream has a direction, east or
west, and a number. Each stream has one slot at every position, and a slot
holds one word or nothing.

In every cycle, every word on a stream moves one position in the stream's
direction. A word that moves past the end of the row is gone. All slots are
empty at cycle 0.

A slice reads from, and places results on, the slots at its own position.
Reading a word does not take it off its stream: the word moves on, and every
slice it passes may read it, each on the cycle the word is at its position.

```
── east ──▶  [0] ─▶ [1] ─▶ [2] ─▶ [3] ─▶ [4] ─▶ [5] ─▶ [6] ─▶ [7] ─▶ [8] ─▶ [9] ─▶ [10] ─▶ [11] ─▶ [12]
             mxm    sxm    mem    mem    mem    mem    vxm    mem    mem    mem    mem     sxm     mxm
◀─ west ──   [0] ◀─ [1] ◀─ [2] ◀─ [3] ◀─ [4] ◀─ [5] ◀─ [6] ◀─ [7] ◀─ [8] ◀─ [9] ◀─ [10] ◀─ [11] ◀─ [12]
```

### 3.3 One cycle

In every cycle each slice executes at most one instruction. A memory slice
may execute two, a read and a write (3.11).

1. The slice reads its operands from the stream slots at its position and
   computes a result.
2. The result enters the slice's pipe. A result stays in the pipe for the
   delay of its instruction and then comes out.
3. Every stream moves one position. The results that came out of the pipes
   are placed on their streams, each at its slice's position.

### 3.4 The timing rule

A result computed by the slice at position `p` on cycle `t` can be read by
the slice at position `q` on cycle

    t + delay + 1 + |q - p|

and on no other cycle, where `delay` is the delay of the instruction that
computed it: its own delay if the machine gives it one, and otherwise the
delay of the kind of the slice at `p`. The stream must run from `p` towards
`q`.

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

A result with a short delay can catch up with an earlier result that has a
longer one. Two results cannot leave one slice on one cycle: an instruction
whose result would leave together with an earlier one makes the machine trap
(3.7), on the cycle it is issued. On a vector slice where multiply has delay
3 and add has delay 1, a multiply on cycle 0 and an add on cycle 2 would
both leave on cycle 3, so the machine traps on cycle 2.

### 3.5 Instructions

An instruction names its operands and its result by stream.

| Kind | Instruction | Effect |
|---|---|---|
| memory | read `addr` to `dst` | the word at `addr` is the result |
| memory | write `src` at `addr` | the word on `src` is stored at `addr` |
| vector, rearrangement | `op` of type `ty`, of `src` to `dst` | a one-value operation |
| vector | `op` of type `ty`, of `a` and `b` to `dst` | a two-value operation |
| vector | constant of type `ty` to `dst` | a value with given elements is the result |
| vector | select of type `ty` by `m` from `a` and `b` to `dst` | element by element, `a` where `m` is not zero and `b` elsewhere |
| matrix | install `g` words at `j` from `src` | the words on `src` and the `g - 1` streams after it become installed words `j` to `j + g - 1` |
| matrix | product of `n` words with `src` to `dst` | a value of type `i32`: element `i` is the dot product of installed word `i` with the word on `src`, for `i` below `n`, and zero from `n` on |

A memory slice moves one word. An instruction of a vector or a rearrangement
slice has a type, and its operands and its result are values of that type,
except where 3.6 says that the result has another. A value of `w` words is
on `w` streams: the stream named and the `w - 1` streams after it, word 0 on
the stream named. "The streams after `src`" are those with the next numbers,
going the same way. The number of the stream named is a multiple of `w`. All
the words of an operand are read on the one cycle, and all the words of a
result leave on the one cycle.

So a value of type `i32` is on streams 0 to 3 or on streams 4 to 7, and a
memory slice reads or writes it one word at a time, on four cycles or in
four slices.

A vector slice of a machine with two streams each way. Streams 0 and 1 going
east hold the words `u` and `v`, and the streams going west hold nothing:

| Instruction | Result |
|---|---|
| relu, of type `i16`, of east 0 to west 0 | the two words of relu of the value (`u`, `v`), for west 0 and 1 |
| relu, of type `i16`, of east 1 to west 0 | trap: bad stream |
| relu, of type `i32`, of east 0 to west 0 | trap: bad stream |
| relu, of type `i8`, of west 0 to east 0 | trap: empty read |

A matrix slice keeps one *installed word* for each lane, numbered from 0.
All are zero at cycle 0. An installed word holds the weights of one element
of a product: the *dot product* of two words is the sum, over the lanes, of
the lane of the one times the lane of the other, each lane read as a signed
integer of 8 bits. The sum is an integer of 32 bits.

Two lanes. Installed word 0 is (1, 2), installed word 1 is (3, 4), and the
stream holds (10, 100):

| Instruction | Result |
|---|---|
| product of 2 words | (210, 430) |
| product of 1 word | (210, 0) |

### 3.6 Operations

One-value operations of the vector slice: relu (negative elements become
zero), requantize by `k` (divide by 2 to the `k`, rounding down, then clamp
to -128 .. 127), widen to a type, negate, absolute value, shift bits left by
`k`, add a constant, multiply by a constant.

The result of requantize is a value of type `i8`, whatever the type of its
operand. The result of widen has the type widened to, which has at least as
many bits as the type of the operand, and the same elements. Every other
result has the type of its instruction.

One-value operations of the rearrangement slice: shift elements by `k`,
rotate elements by `k`, reverse, broadcast element `j`, permute by a table.

Two-value operations of the vector slice: add, subtract, multiply, maximum,
minimum, and, or, exclusive or, less-than (1 or 0 in each element).

### 3.7 Traps

A program that asks for something the machine cannot do makes it *trap*:
it stops, and reports what went wrong, at which slice and on which cycle.
The machine never guesses and never waits.

| Trap | Cause |
|---|---|
| empty read | an instruction read a stream slot that held nothing |
| bad stream | an instruction named a stream that does not exist, or one that a value of that many words cannot start on (3.5) |
| bad address | a memory address or an installed word was out of range |
| wrong slice | an instruction was sent to a slice of the wrong kind |
| two instructions | more instructions were due at one slice on one cycle than it can execute |
| same bank | a read and a write were due at one memory slice on one cycle, for the same bank (3.11) |
| two results | an instruction's result would leave its slice on the same cycle as an earlier result |
| no slice | the program names a slice the machine does not have |

### 3.8 A program for the machine

A program is a list of timed instructions. Each gives a slice, a cycle and an
instruction. There are no branches and no loops.

A timed instruction may repeat, as an entry of a repeater does (2.7): it
gives a number of further issues, a gap, and a stride. From one issue to the
next the address of a memory instruction, or the first installed word of an
install, grows by the stride.

To run a program, the memories are loaded with their starting contents, the
machine runs for a given number of cycles, and the result is the contents of
the memories at the end.

### 3.9 What a slice issues

A slice *issues* words on the cycle on which it runs an instruction that
has a result, or one that writes a word to memory. The words are those of
the result, or the word written. A matrix slice issues nothing when it
installs, and the four words of its product when it multiplies.

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

A memory slice that reads and writes on one cycle (3.11) issues two words on
that cycle: the word read and the word written.

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
| 2 | one-value operation | type, source stream, result stream, the operation |
| 3 | two-value operation | type, the operation, stream `a`, stream `b`, result stream |
| 4 | product | how many installed words, source stream, result stream |
| 5 | install | first installed word, how many, first source stream |
| 6 | constant | type, result stream, how many elements, the elements |
| 7 | select | type, streams `m`, `a`, `b`, result stream |

A type is 0 for `i8`, 1 for `i16` and 2 for `i32`. A stream is the first of
the streams of its value (3.5).

A one-value operation is a number and then what it takes: nothing, `k`, a
signed constant, a type, or a table as its length and its items.

| Operation | Numbers |
|---|---|
| relu | 0 |
| requantize by 3 | 1, 3 |
| negate | 2 |
| absolute value | 3 |
| shift bits left by 2 | 4, 2 |
| add the constant 5 | 5, 10 |
| multiply by the constant -5 | 6, 9 |
| shift elements by 1 | 7, 1 |
| rotate elements by 1 | 8, 1 |
| reverse | 9 |
| broadcast element 2 | 10, 2 |
| permute by the table 1, 0 | 11, 2, 1, 0 |
| widen to `i32` | 12, 2 |

A two-value operation is its number in the order of 3.6, from 0 for add to
8 for less-than.

| Entry | Numbers |
|---|---|
| on cycle 2, read address 0 to stream 0 going east | 2, 0, 0, 0, 0, 0, 0 |
| the same, 3 more times, 3 idle cycles apart, the address growing by 1 | 2, 3, 3, 1, 0, 0, 0 |
| on cycle 9, write stream 0 going west at address 4 | 9, 0, 0, 0, 1, 1, 4 |
| on cycle 6, relu, of type `i8`, of stream 0 going east to stream 0 going west | 6, 0, 0, 0, 2, 0, 0, 1, 0 |
| on cycle 7, add 5 to every element, of type `i8`, of stream 1 going east, to stream 1 going east | 7, 0, 0, 0, 2, 0, 2, 2, 5, 10 |
| on cycle 8, of type `i8`, stream 1 going east minus stream 2 going west, to stream 0 going east | 8, 0, 0, 0, 3, 0, 1, 2, 5, 0 |
| on cycle 8, of type `i32`, streams 0 to 3 going east plus streams 0 to 3 going west, to streams 4 to 7 going east | 8, 0, 0, 0, 3, 2, 0, 0, 1, 8 |
| on cycle 3, stream 0 going east, of type `i8`, widened to `i32`, to streams 4 to 7 going west | 3, 0, 0, 0, 2, 0, 0, 9, 12, 2 |
| on cycle 4, the constant of type `i8` with elements 3 and -4 to stream 2 going west | 4, 0, 0, 0, 6, 0, 5, 2, 6, 7 |
| on cycle 5, install 2 words at 4 from stream 1 going west | 5, 0, 0, 0, 5, 4, 2, 3 |
| on cycle 9, the product of 3 words with stream 0 going west, to streams 4 to 7 going east | 9, 0, 0, 0, 4, 3, 1, 8 |

### 3.11 The two banks of a memory slice

The words of a memory slice are in two *banks*. The lower bank holds the
addresses below a number the machine is described with (3.1), and the upper
bank holds the addresses from that number on.

A memory slice executes a read and a write on one cycle if the two are for
different banks. The result is the word read. Two reads, two writes, or a
read and a write for the same bank cannot be executed on one cycle, and the
machine traps (3.7).

The three slices of 3.4, with two words in each lower bank. The memory at
position 0 reads the word `a` on cycle 0 for a stream going east, and `a` is
at position 2 on cycle 4. The memory at position 2 holds the words `p`, `q`
and `r`:

| On cycle 4 the slice at position 2 is told to | Result |
|---|---|
| write the word on the stream at address 2, and read address 0 | it holds `p`, `q`, `a` |
| write the word on the stream at address 1, and read address 0 | trap: same bank |
| read address 0, and read address 2 | trap: two instructions |

## 4. The cell-level machine

Section 3 treats a slice as one box with a delay. Inside, a slice is built
from the components of section 2.

| Part of a slice | Component |
|---|---|
| issuing the slice's instructions on their cycles | repeater (2.7) |
| the pipe that holds results for their delays | shift register (2.1), as deep as the longest delay of the machine; a result is written into the slot that leaves after its delay |
| the stored words of a memory slice | two memories (2.5), one for each bank (3.11) |
| the installed words and the products of a matrix slice | multiply-accumulate cells (2.3): a row of them for each element of a product, and in a row one cell for each lane of a word. A cell holds one lane of an installed word, and a row adds up its products from cell to cell |

```
repeater (2.7) ──▶ [ slice: mem (2.5) / vxm / sxm / mxm (mac 2.3) ]
                         ▲                                 │
                         │                                 ▼
                   streams (in)               shift register (2.1) ──▶ streams (out)
```

A memory (2.5) takes one command in a cycle. That is why a memory slice can
read and write on one cycle only in different banks.

A machine built this way behaves exactly as section 3 says.
