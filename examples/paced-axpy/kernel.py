"""A loop of three operations, one iteration every three cycles.

    y[i] = requant(a * x[i] + y[i], 3)

One operation is pinned, the last of the body: the requant of iteration i is
issued on cycle 8 + 3 * i. The compiler works backward from each pin, so the
addition is two cycles before it and the multiplication two before that, in
every iteration alike. The vector slice runs three instructions for an
iteration and one in a cycle, so no steady pace is faster than this one.

Without the pin the compiler takes 31 cycles and 28 entries: it fits the
iterations in between each other two at a time, and the result has little
that repeats. With the pin it takes 33 cycles and 10 entries, and it would
take 10 entries for any number of iterations. The pin gives two cycles for a
program a third the size.
"""

import tau
from tau import T


@tau.kernel
def paced_axpy(a: tau.Buf[1], x: tau.Buf[8], y: tau.Buf[8]):
    for i in tau.loop(8):
        scale = tau.load(a, 0)
        product = tau.mul(scale, tau.load(x, i))
        total = tau.add(product, tau.load(y, i))
        tau.store(y, i, tau.requant(total, 3, at=T + 8 + 3 * i))


kernel = paced_axpy
