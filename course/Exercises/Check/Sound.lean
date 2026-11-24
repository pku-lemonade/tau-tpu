/-
Exercise file. Generated from Tau/Proofs/Check/Sound.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Check/Sound.lean.
Build this file alone with:

    lake build Exercises.Check.Sound
-/

import Tau.Check.Checker
import Tau.Proofs.SliceLevel.Map
import Tau.Proofs.IR.Map
import Tau.Proofs.Passes.Simplify

/-!
# The checker is sound

The main result is `check_sound`. If the checker accepts a compiled program for
a kernel, then for every choice of buffer contents:

* the machine runs the program to the end without a trap, and
* the buffers it ends with are exactly the buffers the kernel computes.

The checker ran the machine and the kernel once, on expressions. The proof
turns that single run into a statement about all real inputs. It needs three
facts, each proved elsewhere:

* the machine does not look at its values (`execute_map`),
* a kernel does not look at its values (`Kernel.run_map`),
* simplifying an expression does not change its value (`Expr.denote_simp`).

Evaluating an expression (`Expr.denote`) is a function that respects the
operations, so the first two facts apply to it.
-/

namespace Tau

variable {V W : Type}

/-- Evaluating expressions respects the operations. -/
theorem denote_hom (S : Sem V) (bufs : List (List V)) (fill : V) :
    exprSem.Hom S (Expr.denote S bufs fill) where
  un _ _ := rfl
  bin _ _ _ := rfl
  zero := rfl
  mac _ _ _ _ := rfl

theorem image_map (f : V → W) (map : MemMap) (memSizes : List Nat) (word : Nat → Nat → V)
    (fill : V) :
    (image map memSizes word fill).map (List.map f) =
      image map memSizes (fun b k => f (word b k)) (f fill) := by
  sorry

theorem extract_map (f : V → W) (map : MemMap) (mem : List (List V)) (fill : V) :
    extract map (mem.map (List.map f)) (f fill) = (extract map mem fill).map (List.map f) := by
  sorry

/-- A list is the list of its own elements. -/
theorem range_map_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun k => l[k]?.getD d) = l := by
  sorry

/-- Evaluating the symbolic buffers gives back the real buffers. -/
theorem symBufs_denote (S : Sem V) (bufs : List (List V)) (fill : V) :
    (symBufs (bufs.map List.length)).map (List.map (Expr.denote S bufs fill)) = bufs := by
  sorry

/-- If a kernel run on expressions ends with `e`, then run on real buffers it
ends with `e` evaluated. -/
theorem Kernel.run_of_exprs (S : Sem V) (k : Kernel) (bufs : List (List V)) (fill : V)
    (e : List (List Expr)) (h : kernelExprs k (bufs.map List.length) = some e) :
    k.run S bufs = some (e.map (List.map (Expr.denote S bufs fill))) := by
  sorry

/-- Two tables of expressions that agree after simplification have the same
values. -/
theorem denote_of_simp_eq (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (a b : List (List Expr))
    (h : a.map (·.map Expr.simp) = b.map (·.map Expr.simp)) :
    a.map (List.map (Expr.denote S bufs fill)) =
      b.map (List.map (Expr.denote S bufs fill)) := by
  sorry

/-- **Soundness of the checker.** If `check` accepts the compiled program `c`
for the kernel `k`, then on any buffer contents the machine runs `c` without a
trap and ends with the buffers that `k` computes. -/
theorem check_sound (S : Sem V) (hS : S.Lawful) (k : Kernel) (c : Compiled)
    (bufs : List (List V)) (fill : V)
    (h : check k (bufs.map List.length) c = true) :
    ∃ mem out,
      execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem ∧
      k.run S bufs = some out ∧
      extract c.map mem fill = out := by
  sorry

/-- **Safety.** A program the checker accepts never traps. -/
theorem check_safe (S : Sem V) (hS : S.Lawful) (k : Kernel) (c : Compiled)
    (bufs : List (List V)) (fill : V)
    (h : check k (bufs.map List.length) c = true) :
    ∃ mem, execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem := by
  sorry

end Tau
