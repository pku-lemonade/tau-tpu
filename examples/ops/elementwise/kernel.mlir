// out[i] = max(a[i] + b[i], a[i] - b[i]) for four words, written as a loop.
func.func @elementwise(%a: !tau.buf<4 x 16>, %b: !tau.buf<4 x 16>, %out: !tau.buf<4 x 16>) {
  tau.for 4 {
    %x = tau.load %a[0, 1] : !tau.buf<4 x 16>
    %y = tau.load %b[0, 1] : !tau.buf<4 x 16>
    %s = tau.add %x, %y : !tau.int<16>
    %d = tau.sub %x, %y : !tau.int<16>
    %m = tau.max %s, %d : !tau.int<16>
    tau.store %m, %out[0, 1] : !tau.buf<4 x 16>
  }
  return
}
