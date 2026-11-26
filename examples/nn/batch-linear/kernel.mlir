// One linear layer applied to four inputs: y[i] = relu(requant(W * x[i] + b)).
// The matrix-vector product sits inside a loop, so after unrolling the
// columns of W are streamed to the matrix slice four times.
func.func @batch_linear(%x: !tau.buf<4>, %w: !tau.buf<3>, %b: !tau.buf<1>,
                        %y: !tau.buf<4>) {
  tau.for 4 {
    %0 = tau.load %x[0, 1] : !tau.buf<4>
    %1 = tau.matvec %0, %w[0, 0], 3 : !tau.buf<3>
    %2 = tau.load %b[0, 0] : !tau.buf<1>
    %3 = tau.add %1, %2
    %4 = tau.requant %3, 1
    %5 = tau.relu %4
    tau.store %5, %y[0, 1] : !tau.buf<4>
  }
  return
}
