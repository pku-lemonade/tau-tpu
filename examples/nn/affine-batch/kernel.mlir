// Two affine layers in a loop: y[i] = W[i] * x + b, with a different matrix
// on each iteration. The position of the matrix moves with the loop, so
// tau-unroll has to fill the iteration into a tau.affine.
func.func @affine_batch(%x: !tau.buf<1>, %b: !tau.buf<1>, %w: !tau.buf<4>,
                        %y: !tau.buf<2>) {
  tau.for 2 {
    %0 = tau.load %x[0, 0] : !tau.buf<1>
    %1 = tau.load %b[0, 0] : !tau.buf<1>
    %2 = tau.affine %0, %w[0, 2], 2, %1 : !tau.buf<4>
    tau.store %2, %y[0, 1] : !tau.buf<2>
  }
  return
}
