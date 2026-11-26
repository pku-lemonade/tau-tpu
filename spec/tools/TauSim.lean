import Tau.Tools.Run

/-!
# tau-sim

    tau-sim <stage.json> <buffers.json>

Runs the output of any compiler stage on the given buffer contents and prints
the final buffers as JSON.

* A source program or a kernel is run directly (`Source.run`, `Kernel.run`).
* A placed file has its instructions carried out in order (`Placed.execute`).
* A compiled file is run on the slice-level machine (`execute`).
* An image is decoded (`Image.decode`) and run as a compiled file.

A buffer that the buffers file leaves out starts as zeros. A program's
scratch buffers come after the buffers the user fills, so a buffers file
written for the source program serves every stage.

    tau-sim --timeline <stage.json> <buffers.json>

Prints the events of the run instead: for a source program, a kernel or a
placed program, the word of every pinned operation with its cycle; for a
compiled program, every word a slice issues.

Exits with status 1 if the run fails, for example on a trap.
-/

open Tau

def main (args : List String) : IO UInt32 := do
  -- `--kernel` was once needed to run a kernel file; it is now ignored.
  match args.filter (· != "--kernel") with
  | ["--timeline", spath, bpath] =>
    let st ← Json.orFail spath (Json.stage (← Json.readFile spath))
    let (lanes, bufs) ← Json.orFail bpath (Json.buffers (← Json.readFile bpath))
    match Tools.runStage st lanes bufs with
    | .ok _ =>
      IO.println (Json.ofTimeline (Tools.timelineOf st lanes bufs)).pretty
      pure 0
    | .error e =>
      IO.eprintln e
      pure 1
  | [spath, bpath] =>
    let st ← Json.orFail spath (Json.stage (← Json.readFile spath))
    let (lanes, bufs) ← Json.orFail bpath (Json.buffers (← Json.readFile bpath))
    match Tools.runStage st lanes bufs with
    | .ok out =>
      IO.println (Json.ofBuffers lanes out).pretty
      pure 0
    | .error e =>
      IO.eprintln e
      pure 1
  | _ =>
    IO.eprintln "usage: tau-sim <stage.json> <buffers.json>"
    IO.eprintln "       tau-sim --timeline <stage.json> <buffers.json>"
    pure 2
