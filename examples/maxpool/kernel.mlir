// Max pooling over neighbouring lanes: each lane becomes the larger of itself
// and the next lane, then negative values are removed.
func.func @maxpool(%x: !tau.buf<3>, %out: !tau.buf<3>) {
  tau.for 3 {
    %v = tau.load %x[0, 1] : !tau.buf<3>
    %n = tau.rotate %v, 1
    %m = tau.max %v, %n
    %r = tau.relu %m
    tau.store %r, %out[0, 1] : !tau.buf<3>
  }
  return
}
