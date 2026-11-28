// The axpy example again, compiled for machines/tau9-slow-mul.json, where a
// multiply takes three cycles and every other vector operation one (see the
// file `machine` next to this one).
//
// y[i] = requant(a * x[i] + y[i], 3), updating y in place. Every iteration
// reads a word of y and writes the same word.
func.func @axpy(%a: !tau.buf<1 x 8>, %x: !tau.buf<3 x 8>, %y: !tau.buf<3 x 8>) {
  tau.for 3 {
    %s = tau.load %a[0, 0] : !tau.buf<1 x 8>
    %v = tau.load %x[0, 1] : !tau.buf<3 x 8>
    %w = tau.load %y[0, 1] : !tau.buf<3 x 8>
    %p = tau.mul %s, %v : !tau.int<8>
    %t = tau.add %p, %w : !tau.int<8>
    %r = tau.requant %t, 3 : !tau.int<8>
    tau.store %r, %y[0, 1] : !tau.buf<3 x 8>
  }
  return
}
