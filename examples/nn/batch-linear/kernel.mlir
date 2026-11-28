// One linear layer applied to four inputs: y[i] = relu(requant(W * x[i] + b)).
// The matrix-vector product sits inside a loop. After unrolling there are
// four products with the same matrix: W is installed once and used four
// times.
func.func @batch_linear(%x: !tau.buf<4 x 8>, %w: !tau.buf<3 x 8>, %b: !tau.buf<1 x 32>,
                        %y: !tau.buf<4 x 8>) {
  tau.for 4 {
    %0 = tau.load %x[0, 1] : !tau.buf<4 x 8>
    %1 = tau.matvec %0, %w[0, 0], 3 : !tau.buf<3 x 8>
    %2 = tau.load %b[0, 0] : !tau.buf<1 x 32>
    %3 = tau.add %1, %2 : !tau.int<32>
    %4 = tau.requant %3, 1 : !tau.int<32>
    %5 = tau.relu %4 : !tau.int<8>
    tau.store %5, %y[0, 1] : !tau.buf<4 x 8>
  }
  return
}
