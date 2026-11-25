import Tau.Sim.Run

/-!
# tau-check

    tau-check <kernel.json> <stage.json>

Decides whether the output of a compiler stage computes what the kernel
computes, for all buffer contents. `stage.json` is any file `tauc` writes: a
rewritten kernel, a placed program, or a scheduled or finished program.

Prints `ACCEPT` and exits with status 0, or prints `REJECT` with a reason and
exits with status 1.

The verdict comes from `checkKernels`, `checkPlaced` or `check`, each proved
sound in `Tau/Proofs/Check/`. The reason printed on rejection is extra and is
not covered by a proof.
    tau-check --unroll <before.json> <after.json>

A different question, with no proof behind it: is `after.json` the kernel
that the Lean model of `tau-unroll` (`Kernel.unroll`) gives for `before.json`,
up to the numbering of values? Prints `SAME` and exits with status 0, or
prints `DIFFERENT` and exits with status 1.
-/

open Tau

def main (args : List String) : IO UInt32 := do
  match args with
  | [kpath, spath] =>
    let (sizes, k) ← Json.orFail kpath (Json.kernel (← Json.readFile kpath))
    let st ← Json.orFail spath (Json.stage (← Json.readFile spath))
    if Sim.checkStage k sizes st then
      IO.println "ACCEPT"
      pure 0
    else
      IO.println s!"REJECT: {Sim.explainStage k sizes st}"
      pure 1
  | ["--unroll", bpath, apath] =>
    let (_, before) ← Json.orFail bpath (Json.kernel (← Json.readFile bpath))
    let (_, after) ← Json.orFail apath (Json.kernel (← Json.readFile apath))
    if Sim.sameUnroll before after then
      IO.println "SAME"
      pure 0
    else
      IO.println "DIFFERENT: the compiler's unrolled kernel is not the one the Lean model gives"
      pure 1
  | _ =>
    IO.eprintln "usage: tau-check <kernel.json> <stage.json>"
    IO.eprintln "       tau-check --unroll <before.json> <after.json>"
    pure 2
