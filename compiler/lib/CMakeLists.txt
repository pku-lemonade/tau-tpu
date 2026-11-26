add_mlir_dialect_library(TauDialect
  Dialect/TauDialect.cpp

  DEPENDS
  MLIRTauOpsIncGen

  LINK_LIBS PUBLIC
  MLIRIR
  MLIRSideEffectInterfaces
)

# The machine description and the helpers the passes and writers share.
add_mlir_library(TauSupport
  Support/Machine.cpp
  Support/OpUtils.cpp

  DEPENDS
  MLIRTauOpsIncGen

  LINK_LIBS PUBLIC
  TauDialect
  MLIRFuncDialect
)

# One file for each pass, in the order tauc runs them.
add_mlir_library(TauPasses
  Passes/Inline.cpp
  Passes/Simplify.cpp
  Passes/Unroll.cpp
  Passes/Place.cpp
  Passes/Schedule.cpp
  Passes/Route.cpp
  Passes/Slice.cpp
  Passes/Fold.cpp
  Passes/Encode.cpp
  Passes/Register.cpp

  DEPENDS
  MLIRTauOpsIncGen

  LINK_LIBS PUBLIC
  TauDialect
  TauSupport
  MLIRFuncDialect
  MLIRPass
  MLIRTransformUtils
)

# The writers of the files the Lean tools read.
add_mlir_library(TauEmit
  Emit/EmitSource.cpp
  Emit/EmitMachine.cpp

  DEPENDS
  MLIRTauOpsIncGen

  LINK_LIBS PUBLIC
  TauDialect
  TauSupport
  MLIRFuncDialect
)
