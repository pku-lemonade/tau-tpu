"""Pins that agree, and pins that do not.

`together` pins a load, the relu of it and the store of that, each to the
cycle the timing rule gives it once the load is on cycle 2. The three pins
agree, so the word travels directly from each instruction to the next: read
on 2, relu on 6, written on 9.

`apart` pins the same three operations, but leaves the relu until cycle 30.
No word can spend that long on a stream. So the load is read on its cycle
into a scratch word, the relu reads it back in time for cycle 30, and the
store, pinned four cycles after the relu, takes its result directly. It is
four here and three above because this kernel's output buffer lies one slice
further from the vector slice: what the timing rule gives depends on where
`tau-place` puts the buffers. One cycle less and the compiler refuses.
"""

import tau
from tau import T


@tau.kernel
def together(x: tau.Buf[1], y: tau.Buf[1]):
    v = tau.load(x, 0, at=T + 2)
    r = tau.relu(v, at=T + 6)
    tau.store(y, 0, r, at=T + 9)


@tau.kernel
def apart(x: tau.Buf[1], y: tau.Buf[1]):
    v = tau.load(x, 0, at=T + 2)
    r = tau.relu(v, at=T + 30)
    tau.store(y, 0, r, at=T + 34)


@tau.kernel
def pinned_chain(a: tau.Buf[1], b: tau.Buf[1], c: tau.Buf[1], d: tau.Buf[1]):
    together(a, b)
    apart(c, d, at=T + 20)


kernel = pinned_chain
