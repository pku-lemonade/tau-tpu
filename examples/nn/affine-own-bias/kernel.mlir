// y = W * x + x: the bias of the affine layer is the vector it multiplies.
// The matrix slice takes the same word twice, on two cycles one after the
// other, first as the vector and then as the start of its sum. A word is on a
// stream at one slice for one cycle, so the word is read twice.
func.func @affine_own_bias(%x: !tau.buf<1>, %w: !tau.buf<4>, %y: !tau.buf<1>) {
  %0 = tau.load %x[0, 0] : !tau.buf<1>
  %1 = tau.affine %0, %w[0, 0], 4, %0 : !tau.buf<4>
  tau.store %1, %y[0, 0] : !tau.buf<1>
  return
}
