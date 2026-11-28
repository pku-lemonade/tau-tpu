// Two affine layers in a loop: y[i] = W[i] * x + b, with a different matrix
// on each iteration. The position of the matrix moves with the loop, so
// tau-unroll has to fill the iteration into a tau.matvec, and the matrix
// slice has a new matrix installed for each product.
func.func @affine_batch(%x: !tau.buf<1 x 8>, %b: !tau.buf<1 x 32>, %w: !tau.buf<4 x 8>,
                        %y: !tau.buf<2 x 32>) {
  tau.for 2 {
    %0 = tau.load %x[0, 0] : !tau.buf<1 x 8>
    %1 = tau.load %b[0, 0] : !tau.buf<1 x 32>
    %2 = tau.matvec %0, %w[0, 2], 2 : !tau.buf<4 x 8>
    %3 = tau.add %2, %1 : !tau.int<32>
    tau.store %3, %y[0, 1] : !tau.buf<2 x 32>
  }
  return
}
