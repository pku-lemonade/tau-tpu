// Clamp four words between a lower and an upper bound:
//   out[i] = min(max(a[i], lo), hi)
func.func @clip(%a: !tau.buf<4 x 32>, %lo: !tau.buf<1 x 32>, %hi: !tau.buf<1 x 32>,
                %out: !tau.buf<4 x 32>) {
  tau.for 4 {
    %v = tau.load %a[0, 1] : !tau.buf<4 x 32>
    %l = tau.load %lo[0, 0] : !tau.buf<1 x 32>
    %h = tau.load %hi[0, 0] : !tau.buf<1 x 32>
    %m = tau.max %v, %l : !tau.int<32>
    %r = tau.min %m, %h : !tau.int<32>
    tau.store %r, %out[0, 1] : !tau.buf<4 x 32>
  }
  return
}
