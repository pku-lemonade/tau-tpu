// A quantized linear layer: y = relu(requant(W * x + b)).
//
// %w holds the two columns of W. The second relu is redundant on purpose, to
// give tau-simplify something to remove.
func.func @linear(%x: !tau.buf<1>, %b: !tau.buf<1>, %w: !tau.buf<2>, %y: !tau.buf<1>) {
  %0 = tau.load %x[0, 0] : !tau.buf<1>
  %1 = tau.matvec %0, %w[0, 0], 2 : !tau.buf<2>
  %2 = tau.load %b[0, 0] : !tau.buf<1>
  %3 = tau.add %1, %2
  %4 = tau.requant %3, 0
  %5 = tau.relu %4
  %6 = tau.relu %5
  tau.store %6, %y[0, 0] : !tau.buf<1>
  return
}
