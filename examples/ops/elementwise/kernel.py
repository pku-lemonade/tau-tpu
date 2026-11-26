"""out[i] = max(a[i] + b[i], a[i] - b[i]) for four words, written as a loop."""

import tau


@tau.kernel
def elementwise(a: tau.Buf[4], b: tau.Buf[4], out: tau.Buf[4]):
    for i in tau.loop(4):
        x = tau.load(a, i)
        y = tau.load(b, i)
        s = tau.add(x, y)
        d = tau.sub(x, y)
        m = tau.max(s, d)
        tau.store(out, i, m)


kernel = elementwise
