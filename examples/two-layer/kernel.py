"""Two linear layers, written as one kernel called twice.

`layer` is a kernel: h = relu(requant(W * x + b, shift)). Its matrix product
is pinned to cycle 12 of the layer. `two_layer` calls it once from its own
start and once from cycle 40, with a scratch buffer between the two calls.
So the first product is issued on cycle 12 and the second on cycle 52.

`tau.dense` is not an operation of the machine. It is a Python function that
calls `affine`, `requant` and `relu`, and only those are recorded.
"""

import tau
from tau import T


@tau.kernel
def layer(x: tau.Buf[1], w: tau.Buf["N"], b: tau.Buf[1], y: tau.Buf[1], *,
          N=2, shift=0):
    v = tau.load(x, 0)
    bias = tau.load(b, 0)
    h = tau.dense(v, w, 0, N, bias=bias, shift=shift, at=T + 12)
    tau.store(y, 0, h)


@tau.kernel
def two_layer(x: tau.Buf[1], w1: tau.Buf[2], b1: tau.Buf[1],
              w2: tau.Buf[2], b2: tau.Buf[1], y: tau.Buf[1]):
    hidden = tau.alloc(1)
    layer(x, w1, b1, hidden, shift=1)
    layer(hidden, w2, b2, y, at=T + 40)


kernel = two_layer
