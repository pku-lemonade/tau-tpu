// Two layers in a loop, each with its own matrix: y[i] = W2 * relu(W1 * x[i]).
// Both products run on one matrix slice, which stores the columns of one
// matrix at a time. So the two matrices take turns: each is installed before
// its product and replaced before the other's.
func.func @two_matrices(%x: !tau.buf<2>, %w1: !tau.buf<3>, %w2: !tau.buf<3>,
                        %y: !tau.buf<2>) {
  tau.for 2 {
    %0 = tau.load %x[0, 1] : !tau.buf<2>
    %1 = tau.matvec %0, %w1[0, 0], 3 : !tau.buf<3>
    %h = tau.relu %1
    %2 = tau.matvec %h, %w2[0, 0], 3 : !tau.buf<3>
    tau.store %2, %y[0, 1] : !tau.buf<2>
  }
  return
}
