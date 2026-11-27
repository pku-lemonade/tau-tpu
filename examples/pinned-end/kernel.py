"""A pin at the end of a chain.

Only the last operation is pinned: the negation is issued on cycle 6. The
relu before it and the load before that are not. The compiler works backward
from the pin and puts each exactly as far before its user as the timing rule
says: the relu on cycle 4, the read on cycle 0. So both words travel
directly, and since the read cannot be earlier than cycle 0, cycle 6 is the
earliest the pin can be.

Move the pin to cycle 20 and everything before it moves too: nothing is
issued before cycle 14, and still nothing waits in memory. A pin says when a
word is wanted, and the compiler starts as late as that allows.
"""

import tau
from tau import T


@tau.kernel
def pinned_end(x: tau.Buf[1], y: tau.Buf[1]):
    v = tau.load(x, 0)
    r = tau.relu(v)
    s = tau.neg(r, at=T + 6)
    tau.store(y, 0, s)


kernel = pinned_end
