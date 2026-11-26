"""relu over four words, one word every four cycles.

The loop is pinned: iteration i computes its relu on cycle 6 + 4 * i. One
iteration takes longer than four cycles from its read to its write, so the
iterations overlap, and each slice does the same thing every four cycles.
`tau-fold` turns that into three repeating entries.
"""

import tau
from tau import T


@tau.kernel
def paced(x: tau.Buf[4], y: tau.Buf[4]):
    for i in tau.loop(4):
        v = tau.load(x, i)
        r = tau.relu(v, at=T + 6 + 4 * i)
        tau.store(y, i, r)


kernel = paced
