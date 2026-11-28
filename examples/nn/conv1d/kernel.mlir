// A three-tap convolution along the lanes of a word:
//   out = t0 * x + t1 * shift(x, 1) + t2 * shift(x, 2)
// Each tap is a word holding the same weight in every lane. The shifts run on
// the rearrangement slice.
func.func @conv1d(%x: !tau.buf<2 x 8>, %taps: !tau.buf<3 x 8>, %out: !tau.buf<2 x 8>) {
  tau.for 2 {
    %v = tau.load %x[0, 1] : !tau.buf<2 x 8>
    %t0 = tau.load %taps[0, 0] : !tau.buf<3 x 8>
    %t1 = tau.load %taps[1, 0] : !tau.buf<3 x 8>
    %t2 = tau.load %taps[2, 0] : !tau.buf<3 x 8>
    %s1 = tau.shift %v, 1 : !tau.int<8>
    %s2 = tau.shift %v, 2 : !tau.int<8>
    %p0 = tau.mul %v, %t0 : !tau.int<8>
    %p1 = tau.mul %s1, %t1 : !tau.int<8>
    %p2 = tau.mul %s2, %t2 : !tau.int<8>
    %a = tau.add %p0, %p1 : !tau.int<8>
    %r = tau.add %a, %p2 : !tau.int<8>
    tau.store %r, %out[0, 1] : !tau.buf<2 x 8>
  }
  return
}
