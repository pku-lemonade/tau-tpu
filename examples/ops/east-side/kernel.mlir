// The buffers of this kernel land in the memories east of the vector slice,
// so the compiler uses the matrix and rearrangement slices at the east end
// of the chip. Computes y = min(max(rotate(W * x, 1), lo), hi).
func.func @east_side(%lo: !tau.buf<1>, %hi: !tau.buf<1>, %x: !tau.buf<1>,
                     %w: !tau.buf<2>, %y: !tau.buf<1>) {
  %0 = tau.load %x[0, 0] : !tau.buf<1>
  %1 = tau.matvec %0, %w[0, 0], 2 : !tau.buf<2>
  %2 = tau.rotate %1, 1
  %l = tau.load %lo[0, 0] : !tau.buf<1>
  %3 = tau.max %2, %l
  %h = tau.load %hi[0, 0] : !tau.buf<1>
  %4 = tau.min %3, %h
  tau.store %4, %y[0, 0] : !tau.buf<1>
  return
}
