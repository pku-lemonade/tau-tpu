// Uses the rearrangement slice, and a value (%r) that is used twice, so it
// has to wait in memory.
func.func @shuffle(%a: !tau.buf<2 x 8>, %out: !tau.buf<2 x 8>) {
  %0 = tau.load %a[0, 0] : !tau.buf<2 x 8>
  %1 = tau.load %a[1, 0] : !tau.buf<2 x 8>
  %r = tau.rotate %0, 1 : !tau.int<8>
  %s = tau.shift %1, 2 : !tau.int<8>
  %t = tau.mul %r, %s : !tau.int<8>
  %u = tau.min %r, %t : !tau.int<8>
  tau.store %u, %out[0, 0] : !tau.buf<2 x 8>
  tau.store %r, %out[1, 0] : !tau.buf<2 x 8>
  return
}
