// The buffers of this kernel land in the memories east of the vector slice,
// so the compiler uses the matrix and rearrangement slices at the east end
// of the machine. Computes y = min(max(rotate(W * x, 1), lo), hi).
func.func @east_side(%lo: !tau.buf<1 x 32>, %hi: !tau.buf<1 x 32>, %x: !tau.buf<1 x 8>,
                     %w: !tau.buf<2 x 8>, %y: !tau.buf<1 x 32>) {
  %0 = tau.load %x[0, 0] : !tau.buf<1 x 8>
  %1 = tau.matvec %0, %w[0, 0], 2 : !tau.buf<2 x 8>
  %2 = tau.rotate %1, 1 : !tau.int<32>
  %l = tau.load %lo[0, 0] : !tau.buf<1 x 32>
  %3 = tau.max %2, %l : !tau.int<32>
  %h = tau.load %hi[0, 0] : !tau.buf<1 x 32>
  %4 = tau.min %3, %h : !tau.int<32>
  tau.store %4, %y[0, 0] : !tau.buf<1 x 32>
  return
}
