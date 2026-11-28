# The compiler

| | |
|---|---|
| Describes | What any compiler from programs to the machine has to deliver: the intermediate representations (IRs) a program takes on the way, the steps between them, and what every step must keep. |
| Does not describe | How a step finds its output. The methods and the limits of the compiler in this repository are in `compiler/README.md`, and the Python frontend's in `compiler/python/tau/__init__.py`. |
| Specified in | `spec/Tau/IR/` for the IRs, `spec/Tau/Check/` for what must be kept, `spec/Tau/Isa/Encode.lean` for the image |
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

## 2. Four IRs

On the way a program is written in four *intermediate representations*
(IRs). Each says more than the one before.

| IR | What it has | What it does not have yet |
|---|---|---|
| Source | kernels that call each other; statements, loops, pins | |
| Kernel | one kernel, with no calls | slices, addresses, cycles but for its pins |
| Placed | machine instructions in order, each with a slice; values taken apart into words; an address for every buffer | cycles but for its pins; scratch space; streams |
| Compiled | instructions each with a slice, a cycle and the streams it reads and writes | |

A compiled program is a program for the machine (Machine 3.8). The image
(Machine 3.10) is a compiled program written as numbers.

In each IR a program has the two meanings a program has (Programs 6): the
buffers it ends with, and the words it issues on fixed cycles. In the first
three IRs those are the pinned ones. A compiled program has a cycle for every
instruction, so every word it issues is on a fixed cycle.

## 3. The memory map

A program names buffers; a machine has memories with addresses. The placed and
compiled IRs carry a *memory map*: for every buffer, the memory slice that
holds it and its first address. Loading the buffers into the machine, and
reading them back, go through the map.

A buffer may be in several memory slices. The map then gives it several
*parts*, each a slice and a first address, and its words are dealt out over
the parts in turn: with `g` parts, word `k` is in part `k mod g`, at that
part's first address plus `k / g`, rounded down. A memory slice reads one
word on a cycle, so a buffer in `g` slices can give `g` of its words on one
cycle. A buffer of five words with the parts (slice 2, address 0) and
(slice 3, address 4) has its words 0, 2 and 4 at addresses 0, 1 and 2 of
slice 2, and its words 1 and 3 at addresses 4 and 5 of slice 3.

A buffer of values of `w` words (Programs 1) that has `w` parts has word
`k` of every value in part `k`. All the words of a value can then be read on
one cycle, and written on one cycle.

Memory words that belong to no buffer are scratch space, for words that have
to wait. A placed program has none: its memories hold the buffers and nothing
else. A compiled program has as much as its schedule uses.

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
| place | kernel with no loops | placed | where: the memory and address of each buffer, and the slice that runs each statement. It decides nothing else, and takes every value apart into its words |
| schedule | placed | compiled | when: the cycle of every instruction, and with it which words wait in memory, and in which scratch words |
| route | compiled | compiled | on which stream: the stream of every word, with the words of a value an instruction takes or gives on streams that follow one another (Machine 3.5) |
| slice | compiled | compiled | nothing: each slice's entries, naming streams |
| fold | compiled | compiled | which runs of entries become one repeating entry (Machine 2.7) |
| encode | compiled | image | nothing: the numbers of Machine 3.10 |

A kernel has values and the machine moves words. From the placed IR on a
program names words: a load of a value of `w` words is `w` reads, a store is
`w` writes, and an operation names each word of its operands and of its
result. The words of one value need not stay together. They have to be side
by side only where an instruction takes them as one value.

Place decides nothing about time. In a placed program every word goes from
the instruction that makes it straight to the instructions that use it, and
there may be several of those. A word can wait only in a memory (Machine
3.4), and whether it has to is known only when both its ends have a cycle. So
schedule decides that together with the cycles: it adds the scratch words,
the write that puts a waiting word into one and the reads that take it out.

Schedule gives every word a stream to itself, on a machine with as many streams
as that takes. Route fits the words onto the streams the machine has. So the
cycles can be judged before any stream is shared.

A pin goes with the instructions that issue the words of its value. For a
load those are the reads, for a store the writes, for a matrix product the
instruction that puts the product on its streams.

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

## 8. Keeping to the table

The duty of section 5 does not say which step decides what. The table of
section 4 does, and an output can be held to its row of that table as well,
by comparing its instructions with those of the input, without running
either:

| Step | Its output |
|---|---|
| place | has one instruction for each operation of the kernel, one write for each word of each store, and no scratch space |
| schedule | has the memory map of its input, every operation and every write to a buffer of its input, each on the same slice, and nothing else but reads of buffer words its input reads and writes and reads of scratch words |
| route | is its input with other numbers for the streams |

This is not part of the duty. An output that breaks its row can still be
right (section 6); it has made a decision that belongs to another step. Only
these three rows are written out, because each of these steps adds something
the next one builds on: where, then when, then on which stream.
