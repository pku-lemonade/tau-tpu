// Clamp four words between a lower and an upper bound:
//   out[i] = min(max(a[i], lo), hi)
func.func @clip(%a: !tau.buf<4>, %lo: !tau.buf<1>, %hi: !tau.buf<1>,
                %out: !tau.buf<4>) {
  tau.for 4 {
    %v = tau.load %a[0, 1] : !tau.buf<4>
    %l = tau.load %lo[0, 0] : !tau.buf<1>
    %h = tau.load %hi[0, 0] : !tau.buf<1>
    %m = tau.max %v, %l
    %r = tau.min %m, %h
    tau.store %r, %out[0, 1] : !tau.buf<4>
  }
  return
}
