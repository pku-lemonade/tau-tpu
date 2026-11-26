import VersoManual
import TauBook.StartHere
import TauBook.WorkingInLean
import TauBook.ShiftRegister
import TauBook.Accumulator
import TauBook.Mac
import TauBook.Specifying
import TauBook.PipelineSequencer
import TauBook.Memory
import TauBook.Repeater
import TauBook.SystolicArray
import TauBook.SliceLevel
import TauBook.Kernels
import TauBook.Expressions
import TauBook.Checker
import TauBook.Pins
import TauBook.PythonToImage
import TauBook.CellLevel
import TauBook.EndToEnd
import TauBook.Extending
import TauBook.Tactics
import TauBook.Reading

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Specifying a Tensor Processor in Lean" =>
%%%
authors := ["The tau-tpu authors"]
shortTitle := "tau-tpu"
%%%

This is a self-paced course in writing specifications in Lean 4. It works
through a real development from the bottom up: tau-tpu, a small statically
scheduled machine for tensor programs, a compiler for it, and the proofs that connect
them.

The skill it teaches is turning something that is not Lean, a description of
hardware in words or a compiler pass in C++, into definitions and statements precise
enough to prove things about. The proofs themselves it mostly leaves to an
AI agent, and teaches you to read them and to judge what comes back.

After two introductory chapters, three chapters take a small hardware
component each, read its specification and prove what it does, so that you
know what a proof is. One chapter sets out the method. From then on you
write the specification first: five more components, the machine, the
compiler's input, two of its passes, a rule for its schedules, what it means
to be on time, and how a program becomes numbers. Two chapters read the two
large proofs of the development. One states the result, and one sets
homework: extend the machine.

{include 1 TauBook.StartHere}

{include 1 TauBook.WorkingInLean}

{include 1 TauBook.ShiftRegister}

{include 1 TauBook.Accumulator}

{include 1 TauBook.Mac}

{include 1 TauBook.Specifying}

{include 1 TauBook.PipelineSequencer}

{include 1 TauBook.Memory}

{include 1 TauBook.Repeater}

{include 1 TauBook.SystolicArray}

{include 1 TauBook.SliceLevel}

{include 1 TauBook.Kernels}

{include 1 TauBook.Expressions}

{include 1 TauBook.Checker}

{include 1 TauBook.Pins}

{include 1 TauBook.PythonToImage}

{include 1 TauBook.CellLevel}

{include 1 TauBook.EndToEnd}

{include 1 TauBook.Extending}

{include 1 TauBook.Tactics}

{include 1 TauBook.Reading}
