// The mlp example again, compiled for the 17-slice machine in machines/tau17.json
// (see the file `machine` next to this one).
//
// Two quantized linear layers, three lanes wide:
//   h = relu(requant(W1 * x + b1, 2))
//   y = requant(W2 * h + b2, 1)
// %w1 and %w2 each hold the three columns of a 3 x 3 matrix.
func.func @mlp(%x: !tau.buf<1>, %w1: !tau.buf<3>, %b1: !tau.buf<1>,
               %w2: !tau.buf<3>, %b2: !tau.buf<1>, %y: !tau.buf<1>) {
  %0 = tau.load %x[0, 0] : !tau.buf<1>
  %1 = tau.matvec %0, %w1[0, 0], 3 : !tau.buf<3>
  %2 = tau.load %b1[0, 0] : !tau.buf<1>
  %3 = tau.add %1, %2
  %4 = tau.requant %3, 2
  %h = tau.relu %4
  %5 = tau.matvec %h, %w2[0, 0], 3 : !tau.buf<3>
  %6 = tau.load %b2[0, 0] : !tau.buf<1>
  %7 = tau.add %5, %6
  %8 = tau.requant %7, 1
  tau.store %8, %y[0, 0] : !tau.buf<1>
  return
}
