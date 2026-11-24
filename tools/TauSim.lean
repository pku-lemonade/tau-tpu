import Tau.Sim.Run

/-!
# tau-sim

    tau-sim <stage.json> <buffers.json>

Runs the output of any compiler stage on the given buffer contents and prints
the final buffers as JSON.

* A kernel file is run directly (`Kernel.run`).
* A placed file has its instructions carried out in order (`Placed.execute`).
* A compiled file is run on the slice-level machine (`execute`).

Exits with status 1 if the run fails, for example on a trap.
-/

open Tau

def main (args : List String) : IO UInt32 := do
  -- `--kernel` was once needed to run a kernel file; it is now ignored.
  match args.filter (· != "--kernel") with
  | [spath, bpath] =>
    let st ← Json.orFail spath (Json.stage (← Json.readFile spath))
    let (lanes, bufs) ← Json.orFail bpath (Json.buffers (← Json.readFile bpath))
    match Sim.runStage st lanes bufs with
    | .ok out =>
      IO.println (Json.ofBuffers lanes out).pretty
      pure 0
    | .error e =>
      IO.eprintln e
      pure 1
  | _ =>
    IO.eprintln "usage: tau-sim <stage.json> <buffers.json>"
    pure 2
