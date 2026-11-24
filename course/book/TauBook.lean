import VersoManual
import TauBook.StartHere
import TauBook.ShiftRegister
import TauBook.Accumulator
import TauBook.Mac
import TauBook.PipelineSequencer
import TauBook.Memory
import TauBook.SystolicArray
import TauBook.SliceLevel
import TauBook.Kernels
import TauBook.Expressions
import TauBook.Checker
import TauBook.CellLevel
import TauBook.EndToEnd
import TauBook.Reading

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Specifying a Tensor Processor in Lean" =>
%%%
authors := ["The tau-tpu authors"]
shortTitle := "tau-tpu"
%%%

This is a self-paced course in Lean 4. It teaches Lean by working through a
real development from the bottom up: tau-tpu, a small statically scheduled
tensor processor, a compiler for it, and the proofs that connect them.

Chapters 2 to 7 specify simple hardware components and prove what they do.
Chapter 8 assembles a machine. Chapters 9 to 11 give the compiler's input a
meaning and prove a checker for its output. Chapter 12 opens the machine up
into the components of chapters 2 to 7 and proves nothing changed. Chapter 13
states the result.

{include 1 TauBook.StartHere}

{include 1 TauBook.ShiftRegister}

{include 1 TauBook.Accumulator}

{include 1 TauBook.Mac}

{include 1 TauBook.PipelineSequencer}

{include 1 TauBook.Memory}

{include 1 TauBook.SystolicArray}

{include 1 TauBook.SliceLevel}

{include 1 TauBook.Kernels}

{include 1 TauBook.Expressions}

{include 1 TauBook.Checker}

{include 1 TauBook.CellLevel}

{include 1 TauBook.EndToEnd}

{include 1 TauBook.Reading}
