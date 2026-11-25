import Specs.Tables

/-!
# Read: a pass in C++ beside its copy in Lean

Sources: `compiler/lib/Transforms/Unroll.cpp`, `Tau/Passes/Unroll.lean`,
and `compiler/lib/Target/Schedule.cpp` for the last question.

Do this after `course/Specs/Unroll.lean`. Open the C++ file with line
numbers and the Lean file beside it.

A pass in C++ mixes three things: what it does to the program, what MLIR
needs in order to run it, and what it refuses to handle. A copy in Lean
keeps the first, has nothing for the second, and has to say the third in
some way of its own. Telling the three apart is the first step of specifying
any pass.

For each group of lines below, say what it is about, and if it is about the
kernel or is a limit, name the definition in `Tau/` that says the same
thing. Write the name without `Tau.` in front, for example `"Stmt.inst"`.

    ⟨.mlir, ""⟩            about MLIR; the Lean copy has nothing for it
    ⟨.kernel, "name"⟩      about the kernel; `name` says the same in Lean
    ⟨.limit, "name"⟩       a limit; `name` is where Lean says it

Then answer the four questions at the end, and put the cursor on the two
`#eval` lines.
-/

namespace Specs.ReadCpp

open Tau Specs Specs.Tables

/-- Lines 15 to 23: the `#include` lines and `using namespace mlir`. -/
def lines15to23 : Answer := todo

/-- Lines 28 to 32: `instantiate(OpT op, uint64_t k)`, which sets the base to
`base + stride * k` and the stride to 0. -/
def lines28to32 : Answer := todo

/-- Lines 34 to 43: `instantiate(Operation *op, uint64_t k)`, which picks out
the four operations that have a position. -/
def lines34to43 : Answer := todo

/-- Lines 45 to 51: `struct UnrollPass`, its name and its description. -/
def lines45to51 : Answer := todo

/-- Lines 58 to 61: a `tau.for` inside a `tau.for` is an error. Lines 66 to
69 say the same for the body. -/
def lines58to61 : Answer := todo

/-- Lines 63, 65 and 70: for every `k` below `n`, for every operation of the
body, make a copy and fill in `k`. -/
def lines63and65and70 : Answer := todo

/-- Line 64, and the argument `mapping` on line 70: an `IRMapping`, new for
every copy. -/
def line64 : Answer := todo

/-- Line 73: `loop.erase()`. -/
def line73 : Answer := todo

/-- Lines 80 to 82: `tau::createUnrollPass`. -/
def lines80to82 : Answer := todo

#eval report "Unroll.cpp, group by group"
  (readUnroll lines15to23 lines28to32 lines34to43 lines45to51 lines58to61
    lines63and65and70 line64 line73 lines80to82)

/-! ## Where the two differ

Answer `some true` or `some false`. -/

/-- The C++ gives the statements of each copy of the body new value names,
and the Lean copy keeps the names. (What is line 64 for?) -/
def newNames : Option Bool := todo

/-- Both the C++ and the Lean copy can be given a loop inside a loop. (Look
at the type `Item`.) -/
def nested : Option Bool := todo

/-- A statement outside every loop is changed by the Lean copy and left
alone by the C++. (What does `Item.unroll` do with `.stmt s`?) -/
def outside : Option Bool := todo

/-- The scheduler is not copied in Lean. But one line of
`compiler/lib/Target/Schedule.cpp` is the timing rule of the manual. Its
line number: -/
def timingRuleLine : Nat := todo

#eval report "the differences" (readDifferences newNames nested outside timingRuleLine)

/-! ## After the reports agree

The second group of lines, 34 to 43, names four operations. Until this
exercise was written it named three, and the Lean copy named four. The one
missing was `tau.affine`: inside a loop it kept the same position in every
copy. The checker rejected every such program, so no wrong answer ever came
out of the compiler, and no example had such a kernel. Reading the two files
side by side found it. `examples/affine-batch` is the kernel that now tests
it.

A copy in Lean does not prove the C++ right. It does give you something
precise to hold the C++ against.
-/

end Specs.ReadCpp
