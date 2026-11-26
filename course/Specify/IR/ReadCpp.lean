import Specify.Support.Tables

/-!
# Read: a pass in C++ beside its copy in Lean

Sources: `compiler/lib/Passes/Unroll.cpp`, `spec/Tau/IR/Unroll.lean`,
and `compiler/lib/Passes/Schedule.cpp` for the last question.

Do this after `course/Specify/IR/Unroll.lean`. Open the C++ file with line
numbers and the Lean file beside it.

A pass in C++ mixes three things: what it does to the program, what MLIR
needs in order to run it, and what it refuses to handle. A copy in Lean
keeps the first, has nothing for the second, and has to say the third in
some way of its own. Telling the three apart is the first step of specifying
any pass.

For each group of lines below, say what it is about, and if it is about the
kernel or is a limit, name the definition in `spec/Tau/` that says the same
thing. Write the name without `Tau.` in front, for example `"Stmt.inst"`.

    ⟨.mlir, ""⟩            about MLIR; the Lean copy has nothing for it
    ⟨.kernel, "name"⟩      about the kernel; `name` says the same in Lean
    ⟨.limit, "name"⟩       a limit; `name` is where Lean says it

Then answer the four questions at the end, and put the cursor on the two
`#eval` lines.
-/

namespace Specify.ReadCpp

open Tau Specify Specify.Tables

/-- Lines 16 to 24: the `#include` lines and `using namespace mlir`. -/
def lines16to24 : Answer := todo

/-- Lines 29 to 33: `instantiate(OpT op, uint64_t k)`, which sets the base to
`base + stride * k` and the stride to 0. -/
def lines29to33 : Answer := todo

/-- Lines 35 to 52: `instantiate(Operation *op, uint64_t k)`, which fills the
iteration into a pin and picks out the four operations that have a
position. -/
def lines35to52 : Answer := todo

/-- Lines 54 to 60: `struct UnrollPass`, its name and its description. -/
def lines54to60 : Answer := todo

/-- Lines 67 to 70: a `tau.for` inside a `tau.for` is an error. Lines 75 to
78 say the same for the body. -/
def lines67to70 : Answer := todo

/-- Lines 72, 74 and 79: for every `k` below `n`, for every operation of the
body, make a copy and fill in `k`. -/
def lines72and74and79 : Answer := todo

/-- Line 73, and the argument `mapping` on line 79: an `IRMapping`, new for
every copy. -/
def line73 : Answer := todo

/-- Line 82: `loop.erase()`. -/
def line82 : Answer := todo

/-- Lines 89 to 91: `tau::createUnrollPass`. -/
def lines89to91 : Answer := todo

#eval report "Unroll.cpp, group by group"
  (readUnroll lines16to24 lines29to33 lines35to52 lines54to60 lines67to70
    lines72and74and79 line73 line82 lines89to91)

/-! ## Where the two differ

Answer `some true` or `some false`. -/

/-- The C++ gives the statements of each copy of the body new value names,
and the Lean copy keeps the names. (What is line 73 for?) -/
def newNames : Option Bool := todo

/-- Both the C++ and the Lean copy can be given a loop inside a loop. (Look
at the type `Item`.) -/
def nested : Option Bool := todo

/-- A statement outside every loop is changed by the Lean copy and left
alone by the C++. (What does `Item.unroll` do with `.stmt s`?) -/
def outside : Option Bool := todo

/-- The scheduler is not copied in Lean. But one line of
`compiler/lib/Passes/Schedule.cpp` is the timing rule of the doc. Its
line number: -/
def timingRuleLine : Nat := todo

#eval report "the differences" (readDifferences newNames nested outside timingRuleLine)

/-! ## After the reports agree

The third group of lines, 35 to 52, names four operations. Until this
exercise was written it named three, and the Lean copy named four. The one
missing was `tau.affine`: inside a loop it kept the same position in every
copy. The checker rejected every such program, so no wrong answer ever came
out of the compiler, and no example had such a kernel. Reading the two files
side by side found it. `examples/nn/affine-batch` is the kernel that now tests
it.

A copy in Lean does not prove the C++ right. It does give you something
precise to hold the C++ against.
-/

end Specify.ReadCpp
