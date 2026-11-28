// Two quantized linear layers, three lanes wide:
//   h = relu(requant(W1 * x + b1, 2))
//   y = requant(W2 * h + b2, 1)
// %w1 and %w2 each hold the three rows of a 3 x 3 matrix.
func.func @mlp(%x: !tau.buf<1 x 8>, %w1: !tau.buf<3 x 8>, %b1: !tau.buf<1 x 32>,
               %w2: !tau.buf<3 x 8>, %b2: !tau.buf<1 x 32>, %y: !tau.buf<1 x 8>) {
  %0 = tau.load %x[0, 0] : !tau.buf<1 x 8>
  %1 = tau.matvec %0, %w1[0, 0], 3 : !tau.buf<3 x 8>
  %2 = tau.load %b1[0, 0] : !tau.buf<1 x 32>
  %3 = tau.add %1, %2 : !tau.int<32>
  %4 = tau.requant %3, 2 : !tau.int<32>
  %h = tau.relu %4 : !tau.int<8>
  %5 = tau.matvec %h, %w2[0, 0], 3 : !tau.buf<3 x 8>
  %6 = tau.load %b2[0, 0] : !tau.buf<1 x 32>
  %7 = tau.add %5, %6 : !tau.int<32>
  %8 = tau.requant %7, 1 : !tau.int<32>
  tau.store %8, %y[0, 0] : !tau.buf<1 x 8>
  return
}
