/-
Exercise file. Generated from Tau/Proofs/Check/Sound.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Check/Sound.lean.
Build this file alone with:

    lake build Exercises.Check.Sound
-/

import Tau.Check.Checker
import Tau.Proofs.SliceLevel.Map
import Tau.Proofs.IR.Map
import Tau.Proofs.IR.MemMap
import Tau.Proofs.Check.Simplify

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
operations, so the first two facts apply to it. That gives one lemma for each
side: `Kernel.run_of_exprs` and `execute_of_exprs` say that a run on real
buffers is the run on expressions, evaluated. `denote_of_sameExprs` says that
two tables the checker found equal have equal values. `check_sound` puts the
three together, and so does every theorem in `Tau/Proofs/Check/Passes.lean`.
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
  const _ := rfl
  sel _ _ _ := rfl

/-- A list is the list of its own elements. -/
theorem range_map_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun k => l[k]?.getD d) = l := by
  sorry

/-- Evaluating the symbolic buffers gives back the real buffers. -/
theorem symBufs_denote (S : Sem V) (bufs : List (List V)) (fill : V) :
    (symBufs (bufs.map List.length)).map (List.map (Expr.denote S bufs fill)) = bufs := by
  -- Outline of one proof:
  -- Buffer b of the left side is the list of `bufs[b][k]` for each k, which
  -- is `bufs[b]` by `range_map_getD`. The list of those for each b is
  -- `bufs`, by `range_map_getD` again.
  sorry

/-- If a kernel run on expressions ends with `e`, then run on real buffers it
ends with `e` evaluated. -/
theorem Kernel.run_of_exprs (S : Sem V) (k : Kernel) (bufs : List (List V)) (fill : V)
    (e : List (List Expr)) (h : kernelExprs k (bufs.map List.length) = some e) :
    k.run S bufs = some (e.map (List.map (Expr.denote S bufs fill))) := by
  sorry

/-- Two tables of expressions that are the same after simplifying have the
same values. -/
theorem denote_of_sameExprs (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (a b : List (List Expr)) (h : sameExprs a b = true) :
    a.map (List.map (Expr.denote S bufs fill)) =
      b.map (List.map (Expr.denote S bufs fill)) := by
  -- Outline of one proof:
  -- Simplifying a table and then evaluating it is the same as evaluating it
  -- (`Expr.denote_simp`, under two maps). Rewrite both sides that way.
  sorry

/-- If the machine run on expressions ends with the table `m`, then run on
real buffers it does not trap, and the buffers it ends with are `m`
evaluated. -/
theorem execute_of_exprs (S : Sem V) (c : Compiled) (bufs : List (List V)) (fill : V)
    (m : List (List Expr)) (h : machineExprs c = some m) :
    ∃ mem,
      execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem ∧
      extract c.map mem fill = m.map (List.map (Expr.denote S bufs fill)) := by
  -- Outline of one proof:
  -- Let f evaluate expressions. Unfold `machineExprs` and split on the
  -- symbolic run; if it trapped, `h` is false.
  -- The real memory image is the symbolic one with f applied (`image_map`),
  -- so the real run is the symbolic run with f applied (`execute_map`).
  -- Reading the buffers back commutes with f (`extract_map`).
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
  -- Outline of one proof:
  -- Unfold `check` and split on the two symbolic runs; if either failed,
  -- `h` is false.
  -- The kernel on real buffers is its symbolic run, evaluated
  -- (`Kernel.run_of_exprs`), and so is the machine (`execute_of_exprs`).
  -- The two tables are the same after simplifying, so they are the same
  -- after evaluating (`denote_of_sameExprs`).
  sorry

/-- **Safety.** A program the checker accepts never traps. -/
theorem check_safe (S : Sem V) (hS : S.Lawful) (k : Kernel) (c : Compiled)
    (bufs : List (List V)) (fill : V)
    (h : check k (bufs.map List.length) c = true) :
    ∃ mem, execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem := by
  sorry

end Tau
