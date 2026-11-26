// y[i] = requant(a * x[i] + y[i], 3), updating y in place. Every iteration
// reads a word of y and writes the same word.
func.func @axpy(%a: !tau.buf<1>, %x: !tau.buf<3>, %y: !tau.buf<3>) {
  tau.for 3 {
    %s = tau.load %a[0, 0] : !tau.buf<1>
    %v = tau.load %x[0, 1] : !tau.buf<3>
    %w = tau.load %y[0, 1] : !tau.buf<3>
    %p = tau.mul %s, %v
    %t = tau.add %p, %w
    %r = tau.requant %t, 3
    tau.store %r, %y[0, 1] : !tau.buf<3>
  }
  return
}
