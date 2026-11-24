// Rearranging lanes: reverse a word, copy one lane to all, and permute by a
// table, then combine the three.
func.func @lanes(%a: !tau.buf<1>, %out: !tau.buf<3>) {
  %v = tau.load %a[0, 0] : !tau.buf<1>
  %r = tau.reverse %v
  tau.store %r, %out[0, 0] : !tau.buf<3>
  %b = tau.broadcast %v, 2
  tau.store %b, %out[1, 0] : !tau.buf<3>
  %p = tau.permute %v, [3, 3, 0, 1]
  %q = tau.sub %p, %v
  tau.store %q, %out[2, 0] : !tau.buf<3>
  return
}
