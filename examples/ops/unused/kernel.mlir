// Two operations whose words nothing uses. `tau-simplify` removes the `abs`.
// It keeps the `neg`, because the `neg` is pinned: its word has to be issued
// on cycle 12, used or not.
func.func @unused(%x: !tau.buf<1>, %y: !tau.buf<1>) {
  %v = tau.load %x[0, 0] : !tau.buf<1>
  %r = tau.relu %v
  %a = tau.abs %v
  %n = tau.neg %v at 12
  tau.store %r, %y[0, 0] : !tau.buf<1>
  return
}
