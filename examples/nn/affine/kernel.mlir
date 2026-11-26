// A linear layer whose bias is added inside the matrix slice:
//   y = relu(requant(W * x + b, 1))
// tau.affine starts the accumulator from the bias, so no separate add is
// needed.
func.func @affine(%x: !tau.buf<1>, %w: !tau.buf<4>, %b: !tau.buf<1>,
                  %y: !tau.buf<1>) {
  %0 = tau.load %x[0, 0] : !tau.buf<1>
  %1 = tau.load %b[0, 0] : !tau.buf<1>
  %2 = tau.affine %0, %w[0, 0], 4, %1 : !tau.buf<4>
  %3 = tau.requant %2, 1
  %4 = tau.relu %3
  tau.store %4, %y[0, 0] : !tau.buf<1>
  return
}
