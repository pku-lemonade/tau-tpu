// Lane arithmetic and bit operations on three words:
//   out[i] = (|a[i]| * 3 + 1) xor ((-b[i]) << 2 and a[i] or b[i])
func.func @bitops(%a: !tau.buf<3>, %b: !tau.buf<3>, %out: !tau.buf<3>) {
  tau.for 3 {
    %x = tau.load %a[0, 1] : !tau.buf<3>
    %y = tau.load %b[0, 1] : !tau.buf<3>
    %0 = tau.abs %x
    %1 = tau.muli %0, 3
    %2 = tau.addi %1, 1
    %3 = tau.neg %y
    %4 = tau.shl %3, 2
    %5 = tau.and %4, %x
    %6 = tau.or %5, %y
    %7 = tau.xor %2, %6
    tau.store %7, %out[0, 1] : !tau.buf<3>
  }
  return
}
