import Tau.Sim.Run

/-!
# tau-check

    tau-check <before.json> <after.json>

Decides whether the program in `after.json` computes what the program in
`before.json` computes, for all buffer contents. Each file is any file `tauc`
writes: a kernel, a placed program, or a scheduled or finished program.

| before | after | Check | For |
|---|---|---|---|
| kernel | kernel | `checkKernels` | `tau-simplify`, `tau-unroll` |
| kernel | placed | `checkPlaced` | `tau-place` |
| placed | compiled | `checkScheduled` | `tau-schedule` |
| compiled | compiled | `checkRouted` | `tau-route` |
| kernel | compiled | `check` | the whole compiler |

Prints `ACCEPT` and exits with status 0, or prints `REJECT` with a reason and
exits with status 1.

The verdict comes from the check in the table, each proved sound in
`Tau/Proofs/Check/`. The reason printed on rejection is extra and is not
covered by a proof.

    tau-check --unroll <before.json> <after.json>

A different question, with no proof behind it: is `after.json` the kernel
that the Lean model of `tau-unroll` (`Kernel.unroll`) gives for `before.json`,
up to the numbering of values? Prints `SAME` and exits with status 0, or
prints `DIFFERENT` and exits with status 1.
-/

open Tau

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--unroll", bpath, apath] =>
    let (_, before) ← Json.orFail bpath (Json.kernel (← Json.readFile bpath))
    let (_, after) ← Json.orFail apath (Json.kernel (← Json.readFile apath))
    if Sim.sameUnroll before after then
      IO.println "SAME"
      pure 0
    else
      IO.println "DIFFERENT: the compiler's unrolled kernel is not the one the Lean model gives"
      pure 1
  | [bpath, apath] =>
    let before ← Json.orFail bpath (Json.stage (← Json.readFile bpath))
    let after ← Json.orFail apath (Json.stage (← Json.readFile apath))
    match Sim.checkPair before after with
    | some true =>
      IO.println "ACCEPT"
      pure 0
    | some false =>
      IO.println s!"REJECT: {Sim.explainPair before after}"
      pure 1
    | none =>
      IO.eprintln s!"tau-check: no check compares a {Sim.stageName before} with a {Sim.stageName after}"
      pure 2
  | _ =>
    IO.eprintln "usage: tau-check <before.json> <after.json>"
    IO.eprintln "       tau-check --unroll <before.json> <after.json>"
    pure 2
