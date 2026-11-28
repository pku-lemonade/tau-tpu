// Two operations whose words nothing uses. `tau-simplify` removes the `abs`.
// It keeps the `neg`, because the `neg` is pinned: its word has to be issued
// on cycle 12, used or not.
func.func @unused(%x: !tau.buf<1 x 8>, %y: !tau.buf<1 x 8>) {
  %v = tau.load %x[0, 0] : !tau.buf<1 x 8>
  %r = tau.relu %v : !tau.int<8>
  %a = tau.abs %v : !tau.int<8>
  %n = tau.neg %v at 12 : !tau.int<8>
  tau.store %r, %y[0, 0] : !tau.buf<1 x 8>
  return
}
