import Tau

/-!
Your scratch file. Try things here.

Files in this folder are yours. `course/Work/Foo.lean` is the module
`Work.Foo`, so another file here can use it with `import Work.Foo`.
Check this file from a terminal with `lake build Work.Scratch`.
-/

open Tau

example : (shiftRegister 2 0).trace (fun t => 10 + t) 5 = [0, 0, 10, 11, 12] := by
  decide
