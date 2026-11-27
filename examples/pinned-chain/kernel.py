"""Pins that agree, and pins that do not.

`together` pins a load, the relu of it and the store of that, each to the
cycle the timing rule gives it once the load is on cycle 0: read on 0, relu
on 4, written on 7. The three pins agree, so the word travels directly from
each instruction to the next. These are the cycles the compiler chooses when
nothing is pinned, and no schedule is shorter.

`apart` pins the same three operations of another kernel. Its input buffer
lies next to the vector slice, so its word, read on cycle 0, is there on
cycle 3 and on no other. The relu is pinned to cycle 6. So the word does not
go to the vector slice at first: it is written to a scratch word of the
memory slice it was read from, and read again on cycle 3, in time for cycle
6. That is the least a wait costs here: with the relu on cycle 5 the
compiler refuses, because no word can be in and out of a memory that fast.
The store is pinned four cycles after the relu and takes its result
directly.
"""

import tau
from tau import T


@tau.kernel
def together(x: tau.Buf[1], y: tau.Buf[1]):
    v = tau.load(x, 0, at=T + 0)
    r = tau.relu(v, at=T + 4)
    tau.store(y, 0, r, at=T + 7)


@tau.kernel
def apart(x: tau.Buf[1], y: tau.Buf[1]):
    v = tau.load(x, 0, at=T + 0)
    r = tau.relu(v, at=T + 6)
    tau.store(y, 0, r, at=T + 10)


@tau.kernel
def pinned_chain(a: tau.Buf[1], b: tau.Buf[1], c: tau.Buf[1], d: tau.Buf[1]):
    together(a, b)
    apart(c, d)


kernel = pinned_chain
