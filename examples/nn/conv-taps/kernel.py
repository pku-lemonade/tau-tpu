"""A three-tap filter over a row of words, with the taps as a constant.

    y[i] = requant(taps[0] * x[i] + taps[1] * x[i + 1] + taps[2] * x[i + 2], 2)

The Python `for` over the taps runs while the program is traced: it leaves
three loads, three multiplications and two additions in the body of the
`tau.loop`, and no trace of itself. `TAPS` and `N` are constants of the
kernel, fixed by `specialize` before tracing.
"""

import tau


@tau.kernel
def taps(x: tau.Buf["LEN"], y: tau.Buf["N"], *, N=4, LEN=6, TAPS=(1, 2, 1)):
    for i in tau.loop(N):
        total = None
        for k, tap in enumerate(TAPS):
            term = tau.muli(tau.load(x, i + k), tap)
            total = term if total is None else tau.add(total, term)
        tau.store(y, i, tau.requant(total, 2))


kernel = taps.specialize(N=4, LEN=6, TAPS=(1, 2, 1))
