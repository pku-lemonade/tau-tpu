// The sum of each word and the next: y[i] = x[i] + x[i + 1]. Both operands of
// an add are words of one buffer, so of one memory slice, and they have to
// reach the vector slice on the same cycle. A memory slice reads one word in
// a cycle. So one of the two is read earlier, written to a scratch word of
// another memory slice, and read from there.
func.func @neighbours(%x: !tau.buf<4>, %y: !tau.buf<3>) {
  tau.for 3 {
    %a = tau.load %x[0, 1] : !tau.buf<4>
    %b = tau.load %x[1, 1] : !tau.buf<4>
    %s = tau.add %a, %b
    tau.store %s, %y[0, 1] : !tau.buf<3>
  }
  return
}
