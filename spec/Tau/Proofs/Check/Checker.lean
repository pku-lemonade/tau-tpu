import Tau.Check.Checker
import Tau.Proofs.Machine.Arch
import Tau.Proofs.IR.Kernel
import Tau.Proofs.IR.Source
import Tau.Proofs.IR.Compiled
import Tau.Proofs.IR.MemMap
import Tau.Proofs.Check.Simplify

/-!
# The checker is sound

The main results are `check_sound` and `check_pins`. If the checker accepts
a compiled program for a source program, then for every choice of buffer
contents:

* the machine runs the program to the end without a trap,
* the buffers it ends with are exactly the buffers the source program
  computes (`check_sound`), and
* every word the source program pins to a cycle is issued by the machine on
  that cycle (`check_pins`).

The checker ran the machine and the source program once, on expressions. The
proof turns that single run into a statement about all real inputs. It needs
three facts, each proved elsewhere:

* the machine does not look at its values (`execute_map`, `issues_map`),
* a source program does not look at its values (`Source.run_map`,
  `Source.timeline_map`),
* simplifying an expression does not change its value (`Expr.denote_simp`).

Evaluating an expression (`Expr.denote`) is a function that respects the
operations, so the first two facts apply to it. That gives two lemmas for
each side. `Source.run_of_exprs` and `execute_of_exprs` say that a run on real
buffers is the run on expressions, evaluated; `Source.timeline_of_events` and
`timeline_of_events` say the same of the timelines. `denote_of_sameExprs` says
that two tables the checker found equal have equal values, and
`covers_denote` that a timeline the checker found inside another is inside it
after evaluating. The theorems here and in `spec/Tau/Proofs/Check/Passes.lean` put
these together.
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
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1
    simp [h1]

/-- Evaluating the symbolic buffers gives back the real buffers. -/
theorem symBufs_denote (S : Sem V) (bufs : List (List V)) (fill : V) :
    (symBufs (bufs.map List.length)).map (List.map (Expr.denote S bufs fill)) = bufs := by
  -- Buffer b of the left side is the list of `bufs[b][k]` for each k, which
  -- is `bufs[b]` by `range_map_getD`. The list of those for each b is
  -- `bufs`, by `range_map_getD` again.
  unfold symBufs
  simp only [List.map_map, List.length_map]
  have h : ∀ b, b ∈ List.range bufs.length →
      (List.map (Expr.denote S bufs fill) ∘ fun b =>
        (List.range ((bufs.map List.length)[b]?.getD 0)).map fun k => Expr.init b k) b =
      bufs[b]?.getD [] := by
    intro b hb
    simp only [List.mem_range] at hb
    simp only [Function.comp, List.map_map, List.getElem?_map, List.getElem?_eq_getElem hb,
      Option.map_some, Option.getD_some]
    have hw : (Expr.denote S bufs fill ∘ fun k => Expr.init b k) =
        fun k => bufs[b][k]?.getD fill := by
      funext k
      simp [Function.comp, Expr.denote, bufWord, List.getElem?_eq_getElem hb]
    rw [hw]
    exact range_map_getD bufs[b] fill
  rw [List.map_congr_left h]
  exact range_map_getD bufs []

/-- If a kernel run on expressions ends with `e`, then run on real buffers it
ends with `e` evaluated. -/
theorem Kernel.run_of_exprs (S : Sem V) (k : Kernel) (bufs : List (List V)) (fill : V)
    (e : List (List Expr)) (h : kernelExprs k (bufs.map List.length) = some e) :
    k.run S bufs = some (e.map (List.map (Expr.denote S bufs fill))) := by
  have hb := symBufs_denote S bufs fill
  have hrun := Kernel.run_map exprSem S (Expr.denote S bufs fill) (denote_hom S bufs fill) k
    (symBufs (bufs.map List.length))
  unfold kernelExprs at h
  rw [hb, h] at hrun
  exact hrun

/-- Two tables of expressions that are the same after simplifying have the
same values. -/
theorem denote_of_sameExprs (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (a b : List (List Expr)) (h : sameExprs a b = true) :
    a.map (List.map (Expr.denote S bufs fill)) =
      b.map (List.map (Expr.denote S bufs fill)) := by
  -- Simplifying a table and then evaluating it is the same as evaluating it
  -- (`Expr.denote_simp`, under two maps). Rewrite both sides that way.
  simp only [sameExprs, beq_iff_eq] at h
  have hsimp : ∀ l : List (List Expr),
      (l.map (List.map Expr.simp)).map (List.map (Expr.denote S bufs fill)) =
        l.map (List.map (Expr.denote S bufs fill)) := by
    intro l
    simp only [List.map_map]
    apply List.map_congr_left
    intro row _
    simp only [Function.comp, List.map_map]
    apply List.map_congr_left
    intro e _
    exact Expr.denote_simp S hS bufs fill e
  rw [← hsimp a, h, hsimp]

/-- What `agree` says about the final expressions: both runs finished, and
their tables are the same after simplifying. -/
theorem agree_exprs {a b : Option (List (List Expr))} {ea eb : List (Event Expr)}
    (h : agree a b ea eb = true) : ∃ x y, a = some x ∧ b = some y ∧ sameExprs x y = true := by
  unfold agree at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h, -⟩ := h
  cases a with
  | none => simp at h
  | some x =>
    cases b with
    | none => simp at h
    | some y => exact ⟨x, y, rfl, rfl, h⟩

/-- What `agree` says about the timelines. -/
theorem agree_events {a b : Option (List (List Expr))} {ea eb : List (Event Expr)}
    (h : agree a b ea eb = true) : covers ea eb = true := by
  unfold agree at h
  simp only [Bool.and_eq_true] at h
  exact h.2

/-- Simplifying the word of an event does not change its value. -/
theorem Event.map_denote_simp (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (e : Event Expr) :
    (e.map Expr.simp).map (Expr.denote S bufs fill) = e.map (Expr.denote S bufs fill) := by
  simp only [Event.map, Expr.denote_simp S hS]

/-- A timeline that the checker found inside another is inside it after
evaluating. -/
theorem covers_denote (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (a b : List (Event Expr)) (h : covers a b = true) :
    a.map (Event.map (Expr.denote S bufs fill)) ⊆
      b.map (Event.map (Expr.denote S bufs fill)) := by
  -- Take an event of `a`. Simplified, it is in `b` simplified, so it is the
  -- simplified form of some event of `b`. The two have the same value
  -- (`Event.map_denote_simp`).
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  unfold covers at h
  have hin := List.all_eq_true.mp h (x.map Expr.simp) (List.mem_map.mpr ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hxy⟩ := List.mem_map.mp (List.contains_iff_mem.mp hin)
  refine List.mem_map.mpr ⟨y, hy, ?_⟩
  rw [← Event.map_denote_simp S hS bufs fill y, hxy, Event.map_denote_simp S hS]

/-- If a source program run on expressions ends with `e`, then run on real
buffers it ends with `e` evaluated. -/
theorem Source.run_of_exprs (S : Sem V) (s : Source) (bufs : List (List V)) (fill : V)
    (e : List (List Expr)) (h : sourceExprs s (bufs.map List.length) = some e) :
    s.run S bufs = some (e.map (List.map (Expr.denote S bufs fill))) := by
  have hb := symBufs_denote S bufs fill
  have hrun := Source.run_map exprSem S (Expr.denote S bufs fill) (denote_hom S bufs fill) s
    (symBufs (bufs.map List.length))
  unfold sourceExprs at h
  rw [hb, h] at hrun
  exact hrun

/-- The timeline of a source program on real buffers is its timeline on
expressions, evaluated. -/
theorem Source.timeline_of_events (S : Sem V) (s : Source) (bufs : List (List V)) (fill : V) :
    s.timeline S bufs =
      (sourceEvents s (bufs.map List.length)).map (Event.map (Expr.denote S bufs fill)) := by
  have hb := symBufs_denote S bufs fill
  have ht := Source.timeline_map exprSem S (Expr.denote S bufs fill) (denote_hom S bufs fill) s
    (symBufs (bufs.map List.length))
  rw [hb] at ht
  exact ht

/-- The timeline of a kernel on real buffers is its timeline on expressions,
evaluated. -/
theorem Kernel.timeline_of_events (S : Sem V) (k : Kernel) (bufs : List (List V)) (fill : V) :
    k.timeline S bufs =
      (kernelEvents k (bufs.map List.length)).map (Event.map (Expr.denote S bufs fill)) := by
  have hb := symBufs_denote S bufs fill
  have ht := Kernel.timeline_map exprSem S (Expr.denote S bufs fill) (denote_hom S bufs fill) k
    (symBufs (bufs.map List.length))
  rw [hb] at ht
  exact ht

/-- The memory image for real buffers is the image on expressions,
evaluated. -/
theorem image_denote (S : Sem V) (map : MemMap) (memSizes : List Nat) (bufs : List (List V))
    (fill : V) :
    image map memSizes (bufWord bufs fill) fill =
      (image map memSizes Expr.init .fill).map (List.map (Expr.denote S bufs fill)) := by
  rw [image_map]
  rfl

/-- The timeline of the machine on real buffers is its timeline on
expressions, evaluated. -/
theorem timeline_of_events (S : Sem V) (c : Compiled) (bufs : List (List V)) (fill : V) :
    c.timeline S bufs fill =
      (machineEvents c).map (Event.map (Expr.denote S bufs fill)) := by
  unfold Compiled.timeline machineEvents Compiled.image
  rw [image_denote S, Compiled.timelineFrom_map exprSem S _ (denote_hom S bufs fill)]

/-- If the machine run on expressions ends with the table `m`, then run on
real buffers it does not trap, and the buffers it ends with are `m`
evaluated. -/
theorem execute_of_exprs (S : Sem V) (c : Compiled) (bufs : List (List V)) (fill : V)
    (m : List (List Expr)) (h : machineExprs c = some m) :
    ∃ mem,
      execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem ∧
      extract c.map mem fill = m.map (List.map (Expr.denote S bufs fill)) := by
  -- Let f evaluate expressions. Unfold `machineExprs` and split on the
  -- symbolic run; if it trapped, `h` is false.
  -- The real memory image is the symbolic one with f applied (`image_map`),
  -- so the real run is the symbolic run with f applied (`execute_map`).
  -- Reading the buffers back commutes with f (`extract_map`).
  let f := Expr.denote S bufs fill
  have hf : exprSem.Hom S f := denote_hom S bufs fill
  unfold machineExprs at h
  cases hx : execute exprSem c.cfg c.prog c.cycles (image c.map c.memSizes Expr.init .fill) with
  | error e => simp [hx] at h
  | ok memE =>
    simp only [hx, Option.some.injEq] at h
    have himg : c.image bufs fill =
        (image c.map c.memSizes Expr.init .fill).map (List.map f) := by
      rw [image_map]
      rfl
    refine ⟨memE.map (List.map f), ?_, ?_⟩
    · rw [himg, execute_map exprSem S f hf, hx]
      rfl
    · have hext := extract_map f c.map memE .fill
      rw [h] at hext
      exact hext

/-- **Soundness of the checker.** If `check` accepts the compiled program `c`
for the source program `s`, then on any buffer contents the machine runs `c`
without a trap and ends with the buffers that `s` computes. -/
theorem check_sound (S : Sem V) (hS : S.Lawful) (s : Source) (c : Compiled)
    (bufs : List (List V)) (fill : V)
    (h : check s (bufs.map List.length) c = true) :
    ∃ mem out,
      execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem ∧
      s.run S bufs = some out ∧
      extract c.map mem fill = out := by
  -- `check` says both symbolic runs finished with tables that are the same
  -- after simplifying (`agree_exprs`).
  -- The source program on real buffers is its symbolic run, evaluated
  -- (`Source.run_of_exprs`), and so is the machine (`execute_of_exprs`).
  -- The two tables are the same after simplifying, so they are the same
  -- after evaluating (`denote_of_sameExprs`).
  unfold check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨a, b, hk, hm, hab⟩ := agree_exprs h.2
  obtain ⟨mem, hrun, hx⟩ := execute_of_exprs S c bufs fill b hm
  refine ⟨mem, _, hrun, Source.run_of_exprs S s bufs fill a hk, ?_⟩
  rw [hx]
  exact (denote_of_sameExprs S hS bufs fill a b hab).symm

/-- **The checker and time.** If `check` accepts the compiled program `c` for
the source program `s`, then on any buffer contents every word that `s` pins
to a cycle is issued by the machine on that cycle. -/
theorem check_pins (S : Sem V) (hS : S.Lawful) (s : Source) (c : Compiled)
    (bufs : List (List V)) (fill : V)
    (h : check s (bufs.map List.length) c = true) :
    s.timeline S bufs ⊆ c.timeline S bufs fill := by
  -- Each timeline on real buffers is the timeline on expressions, evaluated
  -- (`Source.timeline_of_events`, `timeline_of_events`). `check` found the
  -- first inside the second, and that survives evaluating (`covers_denote`).
  unfold check at h
  simp only [Bool.and_eq_true] at h
  rw [Source.timeline_of_events S s bufs fill, timeline_of_events S c bufs fill]
  exact covers_denote S hS bufs fill _ _ (agree_events h.2)

/-- **Safety.** A program the checker accepts never traps. -/
theorem check_safe (S : Sem V) (hS : S.Lawful) (s : Source) (c : Compiled)
    (bufs : List (List V)) (fill : V)
    (h : check s (bufs.map List.length) c = true) :
    ∃ mem, execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem := by
  obtain ⟨mem, _, hrun, _, _⟩ := check_sound S hS s c bufs fill h
  exact ⟨mem, hrun⟩

end Tau
