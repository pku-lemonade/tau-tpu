"""Two linear layers, written as one kernel called twice.

`layer` is a kernel: h = relu(requant(W * x + b, shift)). Its matrix product
is pinned to cycle 10 of the layer, the earliest the product can be issued.
`two_layer` calls it once from its own start and once from cycle 22, with a
scratch buffer between the two calls. So the first product is issued on cycle
10 and the second on cycle 32. Cycle 22 is the first from which the second
call can start: one cycle earlier and its input would be read before the
first call has written it. The whole program takes 45 cycles, as many as the
compiler takes when nothing is pinned.

`tau.dense` is not an operation of the machine. It is a Python function that
calls `affine`, `requant` and `relu`, and only those are traced.
"""

import tau
from tau import T


@tau.kernel
def layer(x: tau.Buf[1], w: tau.Buf["N"], b: tau.Buf[1], y: tau.Buf[1], *,
          N=2, shift=0):
    v = tau.load(x, 0)
    bias = tau.load(b, 0)
    h = tau.dense(v, w, 0, N, bias=bias, shift=shift, at=T + 10)
    tau.store(y, 0, h)


@tau.kernel
def two_layer(x: tau.Buf[1], w1: tau.Buf[2], b1: tau.Buf[1],
              w2: tau.Buf[2], b2: tau.Buf[1], y: tau.Buf[1]):
    hidden = tau.alloc(1)
    layer(x, w1, b1, hidden, shift=1)
    layer(hidden, w2, b2, y, at=T + 22)


kernel = two_layer
