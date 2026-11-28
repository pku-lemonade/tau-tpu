// Rearranging lanes: reverse a word, copy one lane to all, and permute by a
// table, then combine the three.
func.func @lanes(%a: !tau.buf<1 x 8>, %out: !tau.buf<3 x 8>) {
  %v = tau.load %a[0, 0] : !tau.buf<1 x 8>
  %r = tau.reverse %v : !tau.int<8>
  tau.store %r, %out[0, 0] : !tau.buf<3 x 8>
  %b = tau.broadcast %v, 2 : !tau.int<8>
  tau.store %b, %out[1, 0] : !tau.buf<3 x 8>
  %p = tau.permute %v, [3, 3, 0, 1] : !tau.int<8>
  %q = tau.sub %p, %v : !tau.int<8>
  tau.store %q, %out[2, 0] : !tau.buf<3 x 8>
  return
}
