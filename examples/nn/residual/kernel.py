"""A residual block: y = relu(x + requant(W2 * relu(requant(W1 * x + b1)))).

The input `x0` is used twice, at the start and at the end.
"""

import tau


@tau.kernel
def residual(x: tau.Buf[1], w1: tau.Buf[4], b1: tau.Buf[1],
             w2: tau.Buf[4], y: tau.Buf[1]):
    x0 = tau.load(x, 0)
    p1 = tau.matvec(x0, w1, 0, 4)
    bias = tau.load(b1, 0)
    h = tau.relu(tau.requant(tau.add(p1, bias), 2))
    p2 = tau.matvec(h, w2, 0, 4)
    out = tau.relu(tau.add(x0, tau.requant(p2, 2)))
    tau.store(y, 0, out)


kernel = residual
