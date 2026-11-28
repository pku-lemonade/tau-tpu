// Two layers in a loop, each with its own matrix:
//   y[i] = W2 * relu(requant(W1 * x[i])).
// Both products run on one matrix slice, which has the rows of one matrix
// installed at a time. So the two matrices take turns: each is installed before
// its product and replaced before the other's.
func.func @two_matrices(%x: !tau.buf<2 x 8>, %w1: !tau.buf<3 x 8>, %w2: !tau.buf<3 x 8>,
                        %y: !tau.buf<2 x 32>) {
  tau.for 2 {
    %0 = tau.load %x[0, 1] : !tau.buf<2 x 8>
    %1 = tau.matvec %0, %w1[0, 0], 3 : !tau.buf<3 x 8>
    %q = tau.requant %1, 0 : !tau.int<32>
    %h = tau.relu %q : !tau.int<8>
    %2 = tau.matvec %h, %w2[0, 0], 3 : !tau.buf<3 x 8>
    tau.store %2, %y[0, 1] : !tau.buf<2 x 32>
  }
  return
}
