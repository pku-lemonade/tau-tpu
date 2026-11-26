// out[i] = max(a[i] + b[i], a[i] - b[i]) for four words, written as a loop.
func.func @elementwise(%a: !tau.buf<4>, %b: !tau.buf<4>, %out: !tau.buf<4>) {
  tau.for 4 {
    %x = tau.load %a[0, 1] : !tau.buf<4>
    %y = tau.load %b[0, 1] : !tau.buf<4>
    %s = tau.add %x, %y
    %d = tau.sub %x, %y
    %m = tau.max %s, %d
    tau.store %m, %out[0, 1] : !tau.buf<4>
  }
  return
}
