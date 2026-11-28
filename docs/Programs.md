# Programs

| | |
|---|---|
| Describes | What a user of tau-tpu writes: buffers and values, statements, loops, calls and pins; and the two things a program promises, what it computes and when. |
| Does not describe | The machine the program runs on ([`Machine.md`](Machine.md)), what the compiler does with the program ([`Compiler.md`](Compiler.md)), or the Python and MLIR notations beyond the table in section 7. |
| Specified in | `spec/Tau/IR/Kernel.lean`, `spec/Tau/IR/Source.lean`, `spec/Tau/Isa/Event.lean` |
| Tables tested by | `course/tests/CourseTest/Docs.lean`, with the rows in `course/Specify/Support/Tables.lean` |

A program is written with no machine in mind. It names buffers, says how values
are loaded from them, combined and stored back, and it may say on which cycle
some of that happens. Slices, streams and addresses are the compiler's
business.

## 1. Buffers and values

A *buffer* is a row of words with a fixed length. A program has a fixed list
of buffers, numbered from 0. Before a run the user fills them; after the run
the user reads them back. That is all a program has to do with the outside.

A *value* is a row of integers of one type, and is 1, 2 or 4 words
(Machine 1). A program never looks inside a value: it cannot test one, and
nothing it does depends on what a value holds.

A statement that produces a value gives it a number. A statement uses the
values of earlier statements by number.

A buffer holds values one after another. For a type of `w` words, position
`k` of a buffer is its `w` words from word `w * k` on. In the notations of
section 7 a buffer has a type, and every load and store of it is of that
type.

## 2. Statements

A program is a list of statements, run in order.

| Statement | Effect |
|---|---|
| load, of type `ty`, from buffer `b` at position `k` | the value at position `k` of buffer `b` is a new value |
| store value `v`, of type `ty`, to buffer `b` at position `k` | position `k` of buffer `b` now holds `v` |
| a one-value operation, of type `ty`, of `v` | the result is a new value |
| a two-value operation, of type `ty`, of `v` and `w` | the result is a new value |
| a constant of type `ty` with given elements | the value with those elements is a new value; missing elements are zero |
| select, of type `ty`, by `m` from `v` and `w` | element by element, `v` where `m` is not zero and `w` elsewhere |
| matrix `M` times `v` | the product is a new value |

The operations are those of Machine 3.6, and compute what is said there. A
statement cannot be run on a value that is not of its type.

A matrix is `n` consecutive words of a buffer, from a given position on. Each
word is a row: it holds the weights of one element of the product. The
product of the matrix with a value `v` of type `i8` is a value of type
`i32`: element `i` is the dot product of row `i` with `v` (Machine 3.5), and
the elements from `n` on are zero.

With buffer 0 holding the words `a` and `b`, and buffer 1 holding `c`, and
every statement of type `i8` but the last:

| Statement | After it |
|---|---|
| load position 1 of buffer 0 | the new value is `b` |
| store the value `b` to position 0 of buffer 1 | buffer 1 holds `b` |
| relu of the value `a` | the new value is relu of `a` |
| the value `a` plus the value `b` | the new value is `a` + `b` |
| load, of type `i16`, position 0 of buffer 0 | the new value is the two words `a` and `b` |

## 3. Loops

A loop runs a list of statements a fixed number of times. On iteration `i`,
counted from 0, a position written `[base, stride]` means `base + stride * i`.
So one loop body can walk along a buffer.

Outside a loop a position is written the same way and `i` is 0.

A loop does not contain another loop.

| Statement, on iteration 1 | After it |
|---|---|
| load `[0, 1]` of buffer 0 | the new value is `b`, the value at position 0 + 1 * 1 |

## 4. Calls

A program may be made of several *kernels*. A kernel is a list of statements
and loops with buffers of its own, and one kernel may call another.

A call names the kernel to run and, for each of that kernel's buffers, the
caller's buffer that it stands for. The called kernel sees only those
buffers, and has its own values: it cannot use a value of its caller, and the
caller cannot use one of its. What the called kernel stores, the caller finds
in its buffers afterwards.

A call does not pass the same buffer twice.

A call is not inside a loop.

A call may give an *origin*, a cycle of the caller. The pins of the called
kernel (section 5) count from it.

A kernel `K` with two buffers: load position 0 of its buffer 0, apply relu,
pinned to cycle 3, and store to position 0 of its buffer 1. A program with
buffers 0, 1 and 2, holding `a`, `b` and `c`:

| Program | Buffers after it | Pinned words |
|---|---|---|
| call `K` on buffers 0 and 2 | `a`, `b`, relu of `a` | relu of `a` on cycle 3 |
| then call `K` on buffers 2 and 1, from cycle 10 | `a`, relu of relu of `a`, relu of `a` | and relu of relu of `a` on cycle 13 |

## 5. Pins

A program does not say when anything happens. The compiler decides. A
program may take that decision back for single statements: a statement may
be *pinned* to a cycle, counted from the start of its kernel. The pin claims
that the words of the statement's value are *issued* on that cycle
(Machine 3.9), every one of them. For a statement with a result the value is
the result. For a store it is the value stored, and the claim names the
buffer and, for each word, its place in the buffer.

Inside a loop a pin may move with the iteration: `at t every d` is cycle
`t + d * i` on iteration `i`.

| Statement | Pin | Iteration | Claims |
|---|---|---|---|
| relu of `a` | at 3 | | relu of `a` is issued on cycle 3 |
| store `a` to position 0 of buffer 1 | at 6 | | `a` is stored to position 0 of buffer 1 on cycle 6 |
| load position 1 of buffer 0, which holds `b` | at 2 | | `b` is issued on cycle 2 |
| relu of `a` | at 5 every 4 | 2 | relu of `a` is issued on cycle 13 |
| store `a` to position `i` of buffer 1 | at 9 every 4 | 3 | `a` is stored to position 3 of buffer 1 on cycle 21 |

The same statements name values of one word. A store of a value of type
`i16`, with the words `a` and `b`, to position 1 of buffer 1, pinned at 6,
claims that `a` is stored to word 2 of buffer 1 on cycle 6 and `b` to word 3
on cycle 6.

A pin names a value and a cycle. It does not name a slice.

Not every set of pins can be met. A word takes a fixed number of cycles to
get from one slice to another (Machine 3.4) and can wait only in a memory. How
far apart two pinned statements have to be depends on the machine and on where
the compiler puts the buffers. A compiler refuses a program whose pins it
cannot meet.

## 6. What a program promises

Two things, and nothing else.

**What it computes.** For any contents of its buffers before the run, the
contents of its buffers after the run.

**When.** For every pinned statement, the words and the cycle.

A program that is run on a machine keeps these promises if, for every contents
of the buffers, the machine ends with the same buffers and issues each pinned
word on its cycle. Statements that are not pinned may happen on any cycle,
in any order that gives the same buffers, on any slice.

A program with scratch buffers, which hold what one kernel leaves for
another, counts them among its buffers. They come after the buffers the user
fills, and the tools fill them with zeros.

## 7. Two ways to write one

A program is written as text in the compiler's `tau` dialect of MLIR, or in
Python. Both say the same things.

| | MLIR | Python |
|---|---|---|
| a kernel | `func.func @k(%x: !tau.buf<4 x 8>)` | `@tau.kernel` on `def k(x: tau.Buf[4])` |
| a buffer of 4 values of type `i32` | `!tau.buf<4 x 32>` | `tau.Buf[4, tau.i32]` |
| load | `%v = tau.load %x[0, 1] : !tau.buf<4 x 8>` | `v = tau.load(x, i)` |
| an operation | `%r = tau.relu %v : !tau.int<8>` | `r = tau.relu(v)` |
| widen | `%w = tau.widen %v : !tau.int<8> to !tau.int<32>` | `w = tau.widen(v, tau.i32)` |
| store | `tau.store %r, %y[0, 1] : !tau.buf<4 x 8>` | `tau.store(y, i, r)` |
| a loop | `tau.for 4 { ... }` | `for i in tau.loop(4):` |
| a pin | `at 6 every 4` after the operation | `at=T + 6 + 4 * i` |
| a call | `tau.call @k(%x, %y) at 40 : (...)` | `k(x, y, at=T + 40)` |
| a scratch buffer | one more argument of the last function | `tau.alloc(1)` |

A buffer is of type `i8` unless it says otherwise. An operation has the type
of its operands, which MLIR writes after it and Python does not write.

In MLIR the program is the last function of the file and the kernels it
calls are the functions before it.

In Python the program is not the text of the function. The function is run
once and the statements it calls are traced; the trace is the program.
Whatever else the function does while it runs, a Python loop, a test on an
integer, a helper function, leaves only the statements it called. `T`
stands for the start cycle of the enclosing kernel, so `at=T + 6 + 4 * i`
pins an operation to cycle `6 + 4 * i` from the kernel's start and
`at=T + 40` sets a call's origin to cycle `40`.
