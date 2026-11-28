// A quantized linear layer: y = relu(requant(W * x + b)).
//
// %w holds the two rows of W. The second relu is redundant on purpose, to
// give tau-simplify something to remove.
func.func @linear(%x: !tau.buf<1 x 8>, %b: !tau.buf<1 x 32>, %w: !tau.buf<2 x 8>, %y: !tau.buf<1 x 8>) {
  %0 = tau.load %x[0, 0] : !tau.buf<1 x 8>
  %1 = tau.matvec %0, %w[0, 0], 2 : !tau.buf<2 x 8>
  %2 = tau.load %b[0, 0] : !tau.buf<1 x 32>
  %3 = tau.add %1, %2 : !tau.int<32>
  %4 = tau.requant %3, 0 : !tau.int<32>
  %5 = tau.relu %4 : !tau.int<8>
  %6 = tau.relu %5 : !tau.int<8>
  tau.store %6, %y[0, 0] : !tau.buf<1 x 8>
  return
}
