// A leaky relu: lanes below zero are divided by 4, the others kept.
//   out[i] = x[i] < 0 ? requant(x[i], 2) : x[i]
// The zero word is a constant, and the choice is a lane-wise select.
func.func @leaky_relu(%x: !tau.buf<3>, %out: !tau.buf<3>) {
  tau.for 3 {
    %v = tau.load %x[0, 1] : !tau.buf<3>
    %z = tau.const [0, 0, 0, 0]
    %m = tau.lt %v, %z
    %s = tau.requant %v, 2
    %r = tau.select %m, %s, %v
    tau.store %r, %out[0, 1] : !tau.buf<3>
  }
  return
}
