"""relu over four words, one word every cycle.

The loop is pinned: iteration i computes its relu on cycle 6 + i. Cycle 6 is
the first on which a word read on cycle 0 can be at the vector slice, and a
memory slice issues one read in a cycle, so no pace is faster. It is also the
schedule the compiler finds when nothing is pinned. The pin costs nothing; it
makes the pace part of the program, and `tau-check` rejects an image that
does not keep it.

One iteration takes eleven cycles from its read to its write, so all four are
under way at once, and each slice does the same thing every cycle. `tau-fold`
turns that into three repeating entries.
"""

import tau
from tau import T


@tau.kernel
def paced(x: tau.Buf[4], y: tau.Buf[4]):
    for i in tau.loop(4):
        v = tau.load(x, i)
        r = tau.relu(v, at=T + 6 + i)
        tau.store(y, i, r)


kernel = paced
