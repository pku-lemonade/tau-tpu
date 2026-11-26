// A residual block: y = relu(x + requant(W2 * relu(requant(W1 * x + b1)))).
// The input %x0 is used twice, at the start and at the end.
func.func @residual(%x: !tau.buf<1>, %w1: !tau.buf<4>, %b1: !tau.buf<1>,
                    %w2: !tau.buf<4>, %y: !tau.buf<1>) {
  %x0 = tau.load %x[0, 0] : !tau.buf<1>
  %0 = tau.matvec %x0, %w1[0, 0], 4 : !tau.buf<4>
  %b = tau.load %b1[0, 0] : !tau.buf<1>
  %1 = tau.add %0, %b
  %2 = tau.requant %1, 2
  %3 = tau.relu %2
  %4 = tau.matvec %3, %w2[0, 0], 4 : !tau.buf<4>
  %5 = tau.requant %4, 2
  %6 = tau.add %x0, %5
  %7 = tau.relu %6
  tau.store %7, %y[0, 0] : !tau.buf<1>
  return
}
