-- The whole library. Each area is listed after the areas it depends on;
-- `spec/README.md` ("The folders") says what is in each.

-- Definitions.

-- Components (Machine 2).
import Tau.Blocks.Basic
import Tau.Blocks.ShiftRegister
import Tau.Blocks.Accumulator
import Tau.Blocks.Mac
import Tau.Blocks.Pipeline
import Tau.Blocks.Memory
import Tau.Blocks.Sequencer
import Tau.Blocks.Repeater
import Tau.Blocks.SystolicArray

-- Words, operations, instructions, events and the image (Machine 1, 3).
import Tau.Isa.Word
import Tau.Isa.Value
import Tau.Isa.Op
import Tau.Isa.Instr
import Tau.Isa.Event
import Tau.Isa.Encode

-- The machine (Machine 3, 4).
import Tau.Machine.SliceLevel
import Tau.Machine.Timing
import Tau.Machine.Issues
import Tau.Machine.CellLevel

-- The IRs of a program (Programs, Compiler 2 to 4).
import Tau.IR.Kernel
import Tau.IR.Source
import Tau.IR.MemMap
import Tau.IR.Placed
import Tau.IR.Compiled
import Tau.IR.Unroll

-- The checks (Compiler 5 to 7).
import Tau.Check.Expr
import Tau.Check.Simplify
import Tau.Check.Checker
import Tau.Check.Passes
import Tau.Check.Decides

-- What the command-line tools call (Formats).
import Tau.Tools.Json
import Tau.Tools.Run

-- Every main statement.
import Tau.Claims

-- Proofs. A proof file has the name of the definition file it is about.

import Tau.Proofs.Blocks.Basic
import Tau.Proofs.Blocks.ShiftRegister
import Tau.Proofs.Blocks.Accumulator
import Tau.Proofs.Blocks.Mac
import Tau.Proofs.Blocks.Pipeline
import Tau.Proofs.Blocks.Memory
import Tau.Proofs.Blocks.Sequencer
import Tau.Proofs.Blocks.Repeater
import Tau.Proofs.Blocks.SystolicArray

import Tau.Proofs.Isa.Word
import Tau.Proofs.Isa.Value
import Tau.Proofs.Isa.Event
import Tau.Proofs.Isa.Encode

import Tau.Proofs.Machine.SliceLevel
import Tau.Proofs.Machine.Timing
import Tau.Proofs.Machine.Issues
import Tau.Proofs.Machine.CellLevel

import Tau.Proofs.IR.Kernel
import Tau.Proofs.IR.Source
import Tau.Proofs.IR.MemMap
import Tau.Proofs.IR.Placed
import Tau.Proofs.IR.Compiled
import Tau.Proofs.IR.Unroll

import Tau.Proofs.Check.Simplify
import Tau.Proofs.Check.Checker
import Tau.Proofs.Check.Passes

-- The two machines joined to the checker, and each statement of
-- `Tau.Claims` proved.
import Tau.Proofs.EndToEnd
import Tau.Proofs.Claims
