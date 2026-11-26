# Programs

| | |
|---|---|
| Describes | What a user of tau-tpu writes: buffers and words, statements, loops, calls and pins; and the two things a program promises, what it computes and when. |
| Does not describe | The machine the program runs on ([`Machine.md`](Machine.md)), what the compiler does with the program ([`Compiler.md`](Compiler.md)), or the Python and MLIR notations beyond the table in section 7. |
| Specified in | `spec/Tau/IR/Kernel.lean`, `spec/Tau/IR/Source.lean`, `spec/Tau/Isa/Event.lean` |
| Tables tested by | `course/tests/CourseTest/Docs.lean`, with the rows in `course/Specify/Support/Tables.lean` |

A program is written with no machine in mind. It names buffers, says how words
are loaded from them, combined and stored back, and it may say on which cycle
some of that happens. Slices, streams and addresses are the compiler's
business.

## 1. Buffers, words and values

A *buffer* is a row of words with a fixed length. A program has a fixed list
of buffers, numbered from 0. Before a run the user fills them; after the run
the user reads them back. That is all a program has to do with the outside.

A *word* is a fixed number of lanes (Machine 1). A program never looks inside a
word: it cannot test one, and nothing it does depends on what a word holds.

A *value* is a word that a statement has produced. Values are numbered. A
statement uses the values of earlier statements by number.

## 2. Statements

A program is a list of statements, run in order.

| Statement | Effect |
|---|---|
| load from buffer `b` at position `k` | the word at position `k` of buffer `b` is a new value |
| store value `v` to buffer `b` at position `k` | position `k` of buffer `b` now holds the word of `v` |
| a one-word operation of `v` | the result is a new value |
| a two-word operation of `v` and `w` | the result is a new value |
| a constant with given lanes | the word with those lanes is a new value; missing lanes are zero |
| select by `m` from `v` and `w` | lane by lane, `v` where `m` is not zero and `w` elsewhere |
| matrix `M` times `v` | the product is a new value |
| matrix `M` times `v`, plus `w` | the product with the word of `w` added |

The operations are those of Machine 3.6, and compute what is said there.

A matrix is `n` consecutive words of a buffer, from a given position on. Each
word is a column. The product of the matrix with a word `v` is the sum, over
`j`, of lane `j` of `v` times column `j`.

With buffer 0 holding the words `a` and `b`, and buffer 1 holding `c`:

| Statement | After it |
|---|---|
| load position 1 of buffer 0 | the new value is `b` |
| store the value `b` to position 0 of buffer 1 | buffer 1 holds `b` |
| relu of the value `a` | the new value is relu of `a` |
| the value `a` plus the value `b` | the new value is `a` + `b` |

## 3. Loops

A loop runs a list of statements a fixed number of times. On iteration `i`,
counted from 0, a position written `[base, stride]` means `base + stride * i`.
So one loop body can walk along a buffer.

Outside a loop a position is written the same way and `i` is 0.

A loop does not contain another loop.

| Statement, on iteration 1 | After it |
|---|---|
| load `[0, 1]` of buffer 0 | the new value is `b`, the word at position 0 + 1 * 1 |

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
that the statement's word is *issued* on that cycle (Machine 3.9). For a
statement with a result the word is the result. For a store it is the word
stored, and the claim names the buffer and the position.

Inside a loop a pin may move with the iteration: `at t every d` is cycle
`t + d * i` on iteration `i`.

| Statement | Pin | Iteration | Claims |
|---|---|---|---|
| relu of `a` | at 3 | | relu of `a` is issued on cycle 3 |
| store `a` to position 0 of buffer 1 | at 6 | | `a` is stored to position 0 of buffer 1 on cycle 6 |
| load position 1 of buffer 0, which holds `b` | at 2 | | `b` is issued on cycle 2 |
| relu of `a` | at 5 every 4 | 2 | relu of `a` is issued on cycle 13 |
| store `a` to position `i` of buffer 1 | at 9 every 4 | 3 | `a` is stored to position 3 of buffer 1 on cycle 21 |

A pin names a word and a cycle. It does not name a slice.

Not every set of pins can be met. A word takes a fixed number of cycles to
get from one slice to another (Machine 3.4) and can wait only in a memory. How
far apart two pinned statements have to be depends on the machine and on where
the compiler puts the buffers. A compiler refuses a program whose pins it
cannot meet.

## 6. What a program promises

Two things, and nothing else.

**What it computes.** For any contents of its buffers before the run, the
contents of its buffers after the run.

**When.** For every pinned statement, the word and the cycle.

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
| a kernel | `func.func @k(%x: !tau.buf<4>)` | `@tau.kernel` on `def k(x: tau.Buf[4])` |
| load | `%v = tau.load %x[0, 1] : !tau.buf<4>` | `v = tau.load(x, i)` |
| an operation | `%r = tau.relu %v` | `r = tau.relu(v)` |
| store | `tau.store %r, %y[0, 1] : !tau.buf<4>` | `tau.store(y, i, r)` |
| a loop | `tau.for 4 { ... }` | `for i in tau.loop(4):` |
| a pin | `at 6 every 4` after the operation | `at=T + 6 + 4 * i` |
| a call | `tau.call @k(%x, %y) at 40 : (...)` | `k(x, y, at=T + 40)` |
| a scratch buffer | one more argument of the last function | `tau.alloc(1)` |

In MLIR the program is the last function of the file and the kernels it
calls are the functions before it.

In Python the program is not the text of the function. The function is run
once and the statements it calls are recorded; the record is the program.
Whatever else the function does while it runs, a Python loop, a test on an
integer, a helper function, leaves only the statements it called. `T`
stands for the start cycle of the enclosing kernel, so `at=T + 6 + 4 * i`
pins an operation to cycle `6 + 4 * i` from the kernel's start and
`at=T + 40` sets a call's origin to cycle `40`.
