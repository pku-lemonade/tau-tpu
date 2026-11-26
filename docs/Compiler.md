# The compiler

| | |
|---|---|
| Describes | What any compiler from programs to the machine has to deliver: the forms a program takes on the way, the steps between them, and what every step must keep. |
| Does not describe | How a step finds its output. The methods and the limits of the compiler in this repository are in `compiler/README.md`, and the Python frontend's in `compiler/python/tau/__init__.py`. |
| Specified in | `spec/Tau/IR/` for the forms, `spec/Tau/Check/` for what must be kept, `spec/Tau/Isa/Encode.lean` for the image |
| Tables tested by | none; this doc has no table of results |

A compiler takes a program ([`Programs.md`](Programs.md)) and a machine
([`Machine.md`](Machine.md)) and gives the numbers the machine is loaded
with. This doc says what that has to achieve. It does not say how, on
purpose: most steps have many right outputs, and the way one is chosen will
change.

## 1. The task

> Put the contents of the program's buffers into the machine's memories, load
> the machine with what the compiler produced, and run it. The machine does not
> trap. When it stops, the memories hold the buffers the program promises,
> and every word the program pins to a cycle was issued on that cycle.

"Promises" is Programs 6. "Issued" is Machine 3.9. "Trap" is Machine 3.7.

This has to hold for every contents of the buffers. A compiler does not see
the contents.

## 2. Four forms

On the way a program takes four forms. Each says more than the one before.

| Form | What it has | What it does not have yet |
|---|---|---|
| Source | kernels that call each other; statements, loops, pins | |
| Kernel | one kernel, with no calls | slices, addresses, cycles but for its pins |
| Placed | machine instructions in order, each with a slice; an address for every buffer | cycles but for its pins; streams |
| Compiled | instructions each with a slice, a cycle and the streams it reads and writes | |

A compiled program is a program for the machine (Machine 3.8). The image
(Machine 3.10) is a compiled program written as numbers.

Each form has the two meanings a program has (Programs 6): the buffers it
ends with, and the words it issues on fixed cycles. For the first three
forms those are the pinned ones. A compiled program has a cycle for every
instruction, so every word it issues is on a fixed cycle.

## 3. The memory map

A program names buffers; a machine has memories with addresses. The placed and
compiled forms carry a *memory map*: for every buffer, the memory slice that
holds it and its first address. Loading the buffers into the machine, and
reading them back, go through the map.

Memory words that belong to no buffer are scratch space, for words that have
to wait.

## 4. The steps

```
Source ─inline─▶ Kernel ─simplify─▶ Kernel ─unroll─▶ Kernel ─place─▶ Placed
                                                                       │
Compiled (scheduled) ◀─────────────────────────── schedule ────────────┘
  │
  └─route─▶ Compiled ─slice─▶ Compiled ─fold─▶ Compiled ─encode─▶ Image
```

| Step | From | To | Decides |
|---|---|---|---|
| inline | source | kernel | nothing: each call is replaced by the kernel it calls |
| simplify | kernel | kernel | which statements can go without changing any result |
| unroll | kernel | kernel with no loops | nothing: each loop is replaced by its iterations |
| place | kernel with no loops | placed | where each buffer lives, which slice runs each statement, which words travel directly and which wait in memory |
| schedule | placed | compiled | the cycle of every instruction |
| route | compiled | compiled | the stream of every word |
| slice | compiled | compiled | nothing: each slice's entries, naming streams |
| fold | compiled | compiled | which runs of entries become one repeating entry (Machine 2.7) |
| encode | compiled | image | nothing: the numbers of Machine 3.10 |

Schedule gives every word a stream to itself, on a machine with as many streams
as that takes. Route fits the words onto the streams the machine has. So the
cycles can be judged before any stream is shared.

A pin goes with the instruction that issues its word. For a load that is the
read, for a store the write, for a matrix product the instruction that puts
the product on a stream.

## 5. What a step must keep

Every step has the same duty, stated on its input and its output:

1. **Buffers.** For every contents of the buffers, the output can be run to
   the end, and it ends with the buffers the input ends with.
2. **Time.** Every word the input issues on a fixed cycle, the output issues
   on that cycle.

The task of section 1 is these two, from the source to the image.

For the steps up to placement, the second duty is about the pins: none may
be lost, and none may move. For scheduling it says that each pinned
instruction is on its cycle. For the steps after it, where every instruction
has a cycle, it says that nothing moves in time at all.

## 6. What a step need not do

A step need not be done in any particular way. Any output that keeps the two
things of section 5 is right. There is no rule here for which slice an
operation should run on, how short a schedule should be, or which entries to
fold.

In particular the duty is about results and cycles, never about
instructions. A schedule may use different instructions from the placed
program it was made from, so long as the buffers and the pinned words come
out the same.

A step may refuse a program: because the machine has too few streams or
memories, or because its pins cannot be met (Programs 5). A refusal is not a
wrong output.

## 7. Judging an output

Whether an output keeps the two things can be decided without knowing how it
was made. Run the input and the output with names in place of words: `a` for
the first word of the first buffer, and so on. Each run ends with an
expression for every word of every buffer, and gives an expression and a
cycle for every word it issues. The output is accepted if the expressions
for the buffers are the same and every issued word of the input is an issued
word of the output, on the same cycle.

```
before ──run on names──▶ Exprs & timeline
                            │  ▲
                    compare │  │
                            ▼  │
after  ──run on names──▶ Exprs & timeline
```

This judges all contents at once, because neither a program nor the machine
ever decides anything from what a word holds (Programs 1, Machine 3.3).

It can reject an output that is right: two expressions can be written
differently and still always have the same value. It never accepts one that
is wrong.
