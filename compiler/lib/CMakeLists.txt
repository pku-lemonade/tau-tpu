add_mlir_dialect_library(TauDialect
  Dialect/TauDialect.cpp

  DEPENDS
  MLIRTauOpsIncGen

  LINK_LIBS PUBLIC
  MLIRIR
  MLIRSideEffectInterfaces
)

add_mlir_library(TauTransforms
  Transforms/Simplify.cpp
  Transforms/Unroll.cpp
  Transforms/Passes.cpp

  DEPENDS
  MLIRTauOpsIncGen

  LINK_LIBS PUBLIC
  TauDialect
  TauTarget
  MLIRFuncDialect
  MLIRPass
  MLIRTransformUtils
)

add_mlir_library(TauTarget
  Target/Chip.cpp
  Target/Emit.cpp
  Target/EmitKernel.cpp
  Target/Place.cpp
  Target/Route.cpp
  Target/Schedule.cpp

  DEPENDS
  MLIRTauOpsIncGen

  LINK_LIBS PUBLIC
  TauDialect
  MLIRFuncDialect
  MLIRPass
)
