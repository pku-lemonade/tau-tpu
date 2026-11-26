// Uses the rearrangement slice, and a value (%r) that is used twice, so it
// has to wait in memory.
func.func @shuffle(%a: !tau.buf<2>, %out: !tau.buf<2>) {
  %0 = tau.load %a[0, 0] : !tau.buf<2>
  %1 = tau.load %a[1, 0] : !tau.buf<2>
  %r = tau.rotate %0, 1
  %s = tau.shift %1, 2
  %t = tau.mul %r, %s
  %u = tau.min %r, %t
  tau.store %u, %out[0, 0] : !tau.buf<2>
  tau.store %r, %out[1, 0] : !tau.buf<2>
  return
}
