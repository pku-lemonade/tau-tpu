"""Two linear layers, written as one kernel called twice.

`layer` is a kernel: h = relu(requant(W * x + b, shift)). Its matrix product
is pinned to cycle 7 of the layer, the earliest the product can be issued:
the two rows of W have to be installed first. `two_layer` calls it once from
its own start and once from cycle 29, with a scratch buffer between the two
calls. So the first product is issued on cycle 7 and the second on cycle 36.
Cycle 29 is the first from which the second call can start: one cycle
earlier and its input would be read before the first call has written it.
The whole program takes 59 cycles, as many as the compiler takes when
nothing is pinned.

`tau.dense` is not an operation of the machine. It is a Python function that
calls `matvec`, `add`, `requant` and `relu`, and only those are traced.
"""

import tau
from tau import T


@tau.kernel
def layer(x: tau.Buf[1], w: tau.Buf["N"], b: tau.Buf[1, tau.i32],
          y: tau.Buf[1], *,
          N=2, shift=0):
    v = tau.load(x, 0)
    bias = tau.load(b, 0)
    h = tau.dense(v, w, 0, N, bias=bias, shift=shift, at=T + 7)
    tau.store(y, 0, h)


@tau.kernel
def two_layer(x: tau.Buf[1], w1: tau.Buf[2], b1: tau.Buf[1, tau.i32],
              w2: tau.Buf[2], b2: tau.Buf[1, tau.i32], y: tau.Buf[1]):
    hidden = tau.alloc(1)
    layer(x, w1, b1, hidden, shift=1)
    layer(hidden, w2, b2, y, at=T + 29)


kernel = two_layer
