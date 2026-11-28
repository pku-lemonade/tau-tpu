// The sum of each word and the next: y[i] = x[i] + x[i + 1]. Both operands of
// an add are words of one buffer, so of one memory slice, and they have to
// reach the vector slice on the same cycle. A memory slice reads one word in
// a cycle. So one of the two is read earlier, written to a scratch word of
// another memory slice, and read from there.
func.func @neighbours(%x: !tau.buf<4 x 8>, %y: !tau.buf<3 x 8>) {
  tau.for 3 {
    %a = tau.load %x[0, 1] : !tau.buf<4 x 8>
    %b = tau.load %x[1, 1] : !tau.buf<4 x 8>
    %s = tau.add %a, %b : !tau.int<8>
    tau.store %s, %y[0, 1] : !tau.buf<3 x 8>
  }
  return
}
