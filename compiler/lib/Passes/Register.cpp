//===- Register.cpp - make the passes available to tau-opt ----------------===//

#include "tau/Passes.h"
#include "tau/Machine.h"

#include "mlir/Pass/Pass.h"
#include "mlir/Pass/PassRegistry.h"

void tau::registerPasses() {
  mlir::registerPass([] { return tau::createInlinePass(); });
  mlir::registerPass([] { return tau::createSimplifyPass(); });
  mlir::registerPass([] { return tau::createUnrollPass(); });
  mlir::registerPass([] { return tau::createPlacePass(Machine::standard()); });
  mlir::registerPass([] { return tau::createSchedulePass(); });
  mlir::registerPass([] { return tau::createRoutePass(); });
  mlir::registerPass([] { return tau::createSlicePass(); });
  mlir::registerPass([] { return tau::createFoldPass(); });
  mlir::registerPass([] { return tau::createEncodePass(); });
}
