// A residual block: y = relu(x + requant(W2 * relu(requant(W1 * x + b1)))).
// The input %x0 is used twice, at the start and at the end.
func.func @residual(%x: !tau.buf<1 x 8>, %w1: !tau.buf<4 x 8>, %b1: !tau.buf<1 x 32>,
                    %w2: !tau.buf<4 x 8>, %y: !tau.buf<1 x 8>) {
  %x0 = tau.load %x[0, 0] : !tau.buf<1 x 8>
  %0 = tau.matvec %x0, %w1[0, 0], 4 : !tau.buf<4 x 8>
  %b = tau.load %b1[0, 0] : !tau.buf<1 x 32>
  %1 = tau.add %0, %b : !tau.int<32>
  %2 = tau.requant %1, 2 : !tau.int<32>
  %3 = tau.relu %2 : !tau.int<8>
  %4 = tau.matvec %3, %w2[0, 0], 4 : !tau.buf<4 x 8>
  %5 = tau.requant %4, 2 : !tau.int<32>
  %6 = tau.add %x0, %5 : !tau.int<8>
  %7 = tau.relu %6 : !tau.int<8>
  tau.store %7, %y[0, 0] : !tau.buf<1 x 8>
  return
}
