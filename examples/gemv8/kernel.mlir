// An 8 x 8 matrix times a vector, with no bias and no activation. Eight
// columns leave memory on eight consecutive cycles.
func.func @gemv8(%x: !tau.buf<1>, %w: !tau.buf<8>, %y: !tau.buf<1>) {
  %0 = tau.load %x[0, 0] : !tau.buf<1>
  %1 = tau.matvec %0, %w[0, 0], 8 : !tau.buf<8>
  tau.store %1, %y[0, 0] : !tau.buf<1>
  return
}
