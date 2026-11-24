//===- tauc.cpp - the tau compiler ----------------------------------------===//
//
//   tauc kernel.mlir -o out [--chip chip.json] [--no-simplify] [--print-mlir]
//
// Runs the passes in order and writes what each one produced, so that each
// can be checked on its own:
//
//   kernel.json      the kernel as the user wrote it
//   simplified.json  after tau-simplify   (a kernel)
//   unrolled.json    after tau-unroll     (a kernel)
//   placed.json      after tau-place      (instructions in order)
//   scheduled.json   after tau-schedule   (timed; one stream per word)
//   compiled.json    after tau-route      (the finished program)
//
// Check any of them against the kernel:
//
//   tau-check out/kernel.json out/placed.json
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Target/Target.h"
#include "tau/Transforms/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/MLIRContext.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Pass/PassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

static cl::opt<std::string> inputFile(cl::Positional, cl::desc("<kernel.mlir>"),
                                      cl::Required);
static cl::opt<std::string> outputDir("o", cl::desc("Output directory"),
                                      cl::value_desc("dir"), cl::init("."));
static cl::opt<std::string> chipFile("chip", cl::desc("Chip description"),
                                     cl::value_desc("chip.json"));
static cl::opt<bool> noSimplify("no-simplify",
                                cl::desc("Do not run tau-simplify"));
static cl::opt<bool> printMLIR("print-mlir",
                               cl::desc("Print the function after each pass"));

static int fail(const Twine &message) {
  errs() << "tauc: " << message << "\n";
  return 1;
}

static bool write(StringRef name, Expected<json::Value> value) {
  if (!value) {
    errs() << "tauc: " << name << ": " << toString(value.takeError()) << "\n";
    return false;
  }
  SmallString<128> path(outputDir);
  sys::path::append(path, name);
  std::error_code ec;
  raw_fd_ostream out(path, ec);
  if (ec) {
    errs() << "tauc: cannot write " << path << ": " << ec.message() << "\n";
    return false;
  }
  out << formatv("{0:2}", *value) << "\n";
  return true;
}

int main(int argc, char **argv) {
  InitLLVM init(argc, argv);
  cl::ParseCommandLineOptions(argc, argv, "tau compiler\n");

  tau::Chip chip = tau::Chip::standard();
  if (!chipFile.empty()) {
    Expected<tau::Chip> read = tau::Chip::fromFile(chipFile);
    if (!read)
      return fail(chipFile + ": " + toString(read.takeError()));
    chip = std::move(*read);
  }

  mlir::MLIRContext context;
  context.loadDialect<tau::TauDialect, mlir::func::FuncDialect>();
  mlir::OwningOpRef<mlir::ModuleOp> module =
      mlir::parseSourceFile<mlir::ModuleOp>(inputFile, &context);
  if (!module)
    return 1;

  auto funcs = module->getOps<mlir::func::FuncOp>();
  if (funcs.empty() || std::next(funcs.begin()) != funcs.end())
    return fail("expected exactly one function");
  mlir::func::FuncOp func = *funcs.begin();

  if (std::error_code ec = sys::fs::create_directories(outputDir))
    return fail("cannot create " + outputDir + ": " + ec.message());

  // Run one pass and show the result if asked.
  auto run = [&](StringRef name, std::unique_ptr<mlir::Pass> pass) {
    mlir::PassManager manager(&context);
    manager.addNestedPass<mlir::func::FuncOp>(std::move(pass));
    if (mlir::failed(manager.run(*module))) {
      errs() << "tauc: " << name << " failed\n";
      return false;
    }
    if (printMLIR) {
      outs() << "// after " << name << "\n";
      module->print(outs());
      outs() << "\n";
    }
    return true;
  };

  if (!write("kernel.json", tau::emitKernel(func)))
    return 1;

  if (!noSimplify && !run("tau-simplify", tau::createSimplifyPass()))
    return 1;
  if (!write("simplified.json", tau::emitKernel(func)))
    return 1;

  if (!run("tau-unroll", tau::createUnrollPass()) ||
      !write("unrolled.json", tau::emitKernel(func)))
    return 1;

  if (!run("tau-place", tau::createPlacePass(chip)) ||
      !write("placed.json", tau::emitPlaced(func)))
    return 1;

  if (!run("tau-schedule", tau::createSchedulePass()) ||
      !write("scheduled.json", tau::emitCompiled(func, /*idealRouting=*/true)))
    return 1;

  if (!run("tau-route", tau::createRoutePass()) ||
      !write("compiled.json", tau::emitCompiled(func, /*idealRouting=*/false)))
    return 1;
  return 0;
}
