//===- tauc.cpp - the tau compiler ----------------------------------------===//
//
//   tauc kernel.mlir -o out [--machine machine.json] [--no-simplify] [--print-mlir]
//
// Runs the passes in order and writes what each one produced, so that each
// can be checked on its own:
//
//   source.json      the program as written, calls and all
//   inlined.json     after tau-inline     (a kernel)
//   simplified.json  after tau-simplify   (a kernel)
//   unrolled.json    after tau-unroll     (a kernel)
//   placed.json      after tau-place      (instructions in order)
//   scheduled.json   after tau-schedule   (timed; a stream for every word)
//   routed.json      after tau-route      (timed, on the machine's streams)
//   sliced.json      after tau-slice      (entries, slice by slice)
//   compiled.json    after tau-fold       (the finished program)
//   image.json       after tau-encode     (the finished program as numbers)
//
// The program is the last function of the file. The functions before it are
// kernels it may call.
//
// Check any of them against the one before, or against the source:
//
//   tau-check out/source.json out/image.json
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Emit.h"
#include "tau/Machine.h"
#include "tau/Passes.h"

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
static cl::opt<std::string> machineFile("machine", cl::desc("Machine description"),
                                     cl::value_desc("machine.json"));
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

  tau::Machine machine = tau::Machine::standard();
  if (!machineFile.empty()) {
    Expected<tau::Machine> read = tau::Machine::fromFile(machineFile);
    if (!read)
      return fail(machineFile + ": " + toString(read.takeError()));
    machine = std::move(*read);
  }

  mlir::MLIRContext context;
  context.loadDialect<tau::TauDialect, mlir::func::FuncDialect>();
  mlir::OwningOpRef<mlir::ModuleOp> module =
      mlir::parseSourceFile<mlir::ModuleOp>(inputFile, &context);
  if (!module)
    return 1;

  // The program is the last function.
  auto program = [&]() -> mlir::func::FuncOp {
    mlir::func::FuncOp last;
    for (mlir::func::FuncOp func : module->getOps<mlir::func::FuncOp>())
      last = func;
    return last;
  };
  if (!program())
    return fail("expected at least one function");

  if (std::error_code ec = sys::fs::create_directories(outputDir))
    return fail("cannot create " + outputDir + ": " + ec.message());

  // Run one pass and show the result if asked.
  auto show = [&](StringRef name) {
    if (printMLIR) {
      outs() << "// after " << name << "\n";
      module->print(outs());
      outs() << "\n";
    }
  };
  auto run = [&](StringRef name, std::unique_ptr<mlir::Pass> pass) {
    mlir::PassManager manager(&context);
    manager.addNestedPass<mlir::func::FuncOp>(std::move(pass));
    if (mlir::failed(manager.run(*module))) {
      errs() << "tauc: " << name << " failed\n";
      return false;
    }
    show(name);
    return true;
  };

  if (!write("source.json", tau::emitSource(program())))
    return 1;

  // tau-inline is a pass on the module: it removes the kernels it copies in.
  {
    mlir::PassManager manager(&context);
    manager.addPass(tau::createInlinePass());
    if (mlir::failed(manager.run(*module))) {
      errs() << "tauc: tau-inline failed\n";
      return 1;
    }
    show("tau-inline");
  }
  mlir::func::FuncOp func = program();
  if (!write("inlined.json", tau::emitSource(func)))
    return 1;

  if (!noSimplify && !run("tau-simplify", tau::createSimplifyPass()))
    return 1;
  if (!write("simplified.json", tau::emitSource(func)))
    return 1;

  if (!run("tau-unroll", tau::createUnrollPass()) ||
      !write("unrolled.json", tau::emitSource(func)))
    return 1;

  if (!run("tau-place", tau::createPlacePass(machine)) ||
      !write("placed.json", tau::emitPlaced(func)))
    return 1;

  if (!run("tau-schedule", tau::createSchedulePass()) ||
      !write("scheduled.json", tau::emitCompiled(func)))
    return 1;

  if (!run("tau-route", tau::createRoutePass()) ||
      !write("routed.json", tau::emitCompiled(func)))
    return 1;

  if (!run("tau-slice", tau::createSlicePass()) ||
      !write("sliced.json", tau::emitCompiled(func)))
    return 1;

  if (!run("tau-fold", tau::createFoldPass()) ||
      !write("compiled.json", tau::emitCompiled(func)))
    return 1;

  if (!run("tau-encode", tau::createEncodePass()) ||
      !write("image.json", tau::emitImage(func)))
    return 1;
  return 0;
}
