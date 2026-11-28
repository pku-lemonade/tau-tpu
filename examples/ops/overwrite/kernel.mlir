// A running sum kept in place: acc[0] = acc[0] + a[i], four times. Every
// iteration reads the word the previous iteration wrote. The last two lines
// load a word, overwrite it, and then use the old value.
func.func @overwrite(%a: !tau.buf<4 x 8>, %acc: !tau.buf<1 x 8>, %old: !tau.buf<1 x 8>) {
  tau.for 4 {
    %s = tau.load %acc[0, 0] : !tau.buf<1 x 8>
    %x = tau.load %a[0, 1] : !tau.buf<4 x 8>
    %t = tau.add %s, %x : !tau.int<8>
    tau.store %t, %acc[0, 0] : !tau.buf<1 x 8>
  }
  %before = tau.load %acc[0, 0] : !tau.buf<1 x 8>
  %first = tau.load %a[0, 0] : !tau.buf<4 x 8>
  tau.store %first, %acc[0, 0] : !tau.buf<1 x 8>
  %r = tau.relu %before : !tau.int<8>
  tau.store %r, %old[0, 0] : !tau.buf<1 x 8>
  return
}
