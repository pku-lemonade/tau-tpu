//===- tau-opt.cpp - run tau passes on MLIR text --------------------------===//
//
//   tau-opt kernel.mlir --tau-simplify --tau-unroll
//
// Reads a module, runs the requested passes, and prints the result. Use it to
// see what each pass does.
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Transforms/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/DialectRegistry.h"
#include "mlir/Tools/mlir-opt/MlirOptMain.h"

int main(int argc, char **argv) {
  mlir::DialectRegistry registry;
  registry.insert<tau::TauDialect, mlir::func::FuncDialect>();
  tau::registerPasses();
  return mlir::asMainReturnCode(
      mlir::MlirOptMain(argc, argv, "tau pass driver\n", registry));
}
