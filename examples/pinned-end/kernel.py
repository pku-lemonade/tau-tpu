"""A pin at the end of a chain.

Only the last operation is pinned: the negation is issued on cycle 20. The
relu before it and the load before that are not. The compiler works backward
from the pin and puts each as late as it can be, which is exactly as far
before its user as the timing rule says. So both words travel directly, and
nothing is issued before cycle 14.

Left to run as early as it could, the relu would be issued on cycle 4 and
its word would be at the vector slice again on cycle 6, fourteen cycles
before the negation reads it. It would have to wait in memory.
"""

import tau
from tau import T


@tau.kernel
def pinned_end(x: tau.Buf[1], y: tau.Buf[1]):
    v = tau.load(x, 0)
    r = tau.relu(v)
    s = tau.neg(r, at=T + 20)
    tau.store(y, 0, s)


kernel = pinned_end
