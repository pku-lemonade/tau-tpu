// A three-tap convolution along the lanes of a word:
//   out = t0 * x + t1 * shift(x, 1) + t2 * shift(x, 2)
// Each tap is a word holding the same weight in every lane. The shifts run on
// the rearrangement slice.
func.func @conv1d(%x: !tau.buf<2>, %taps: !tau.buf<3>, %out: !tau.buf<2>) {
  tau.for 2 {
    %v = tau.load %x[0, 1] : !tau.buf<2>
    %t0 = tau.load %taps[0, 0] : !tau.buf<3>
    %t1 = tau.load %taps[1, 0] : !tau.buf<3>
    %t2 = tau.load %taps[2, 0] : !tau.buf<3>
    %s1 = tau.shift %v, 1
    %s2 = tau.shift %v, 2
    %p0 = tau.mul %v, %t0
    %p1 = tau.mul %s1, %t1
    %p2 = tau.mul %s2, %t2
    %a = tau.add %p0, %p1
    %r = tau.add %a, %p2
    tau.store %r, %out[0, 1] : !tau.buf<2>
  }
  return
}
