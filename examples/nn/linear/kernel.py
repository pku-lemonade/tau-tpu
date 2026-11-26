"""A quantized linear layer: y = relu(requant(W * x + b)).

`w` holds the two columns of W. The second `relu` is redundant on purpose, to
give `tau-simplify` something to remove.
"""

import tau


@tau.kernel
def linear(x: tau.Buf[1], b: tau.Buf[1], w: tau.Buf[2], y: tau.Buf[1]):
    v = tau.load(x, 0)
    prod = tau.matvec(v, w, 0, 2)
    bias = tau.load(b, 0)
    acc = tau.add(prod, bias)
    q = tau.requant(acc, 0)
    r = tau.relu(q)
    r = tau.relu(r)
    tau.store(y, 0, r)


kernel = linear
