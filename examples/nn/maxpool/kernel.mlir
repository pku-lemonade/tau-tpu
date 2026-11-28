// Max pooling over neighbouring lanes: each lane becomes the larger of itself
// and the next lane, then negative values are removed.
func.func @maxpool(%x: !tau.buf<3 x 8>, %out: !tau.buf<3 x 8>) {
  tau.for 3 {
    %v = tau.load %x[0, 1] : !tau.buf<3 x 8>
    %n = tau.rotate %v, 1 : !tau.int<8>
    %m = tau.max %v, %n : !tau.int<8>
    %r = tau.relu %m : !tau.int<8>
    tau.store %r, %out[0, 1] : !tau.buf<3 x 8>
  }
  return
}
