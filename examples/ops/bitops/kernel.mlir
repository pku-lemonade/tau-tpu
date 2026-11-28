// Lane arithmetic and bit operations on three words:
//   out[i] = (|a[i]| * 3 + 1) xor ((-b[i]) << 2 and a[i] or b[i])
func.func @bitops(%a: !tau.buf<3 x 16>, %b: !tau.buf<3 x 16>, %out: !tau.buf<3 x 16>) {
  tau.for 3 {
    %x = tau.load %a[0, 1] : !tau.buf<3 x 16>
    %y = tau.load %b[0, 1] : !tau.buf<3 x 16>
    %0 = tau.abs %x : !tau.int<16>
    %1 = tau.muli %0, 3 : !tau.int<16>
    %2 = tau.addi %1, 1 : !tau.int<16>
    %3 = tau.neg %y : !tau.int<16>
    %4 = tau.shl %3, 2 : !tau.int<16>
    %5 = tau.and %4, %x : !tau.int<16>
    %6 = tau.or %5, %y : !tau.int<16>
    %7 = tau.xor %2, %6 : !tau.int<16>
    tau.store %7, %out[0, 1] : !tau.buf<3 x 16>
  }
  return
}
