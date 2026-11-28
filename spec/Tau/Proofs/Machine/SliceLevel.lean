import Tau.Machine.SliceLevel
import Tau.Proofs.Isa.Event

/-!
# The machine does not look at its values

The machine moves words around and hands them to the operations in `Sem`. It
never inspects a word to decide what to do next: which slots are read, which
are written, and whether it traps depend only on the program.

This file states that precisely. Take two kinds of value, `V` and `W`, and a
function `f : V → W` that respects the operations (`Sem.Hom`). Then running the
machine on `V`-values and applying `f` to the final state gives the same result
as applying `f` to the starting state and running the machine on `W`-values.
That is `run_map`, and `execute_map` is the same fact for memory contents.

The checker's proof uses this with `V` the expressions, `W` the real words and
`f` the function that evaluates an expression.
-/

namespace Tau

variable {V W : Type}

/-- Apply `f` to every value in a slice. -/
def Slice.map (f : V → W) (sl : Slice V) : Slice W where
  words := sl.words.map f
  weights := sl.weights.map f
  pipe := sl.pipe.map (Option.map (Prod.map id (List.map f)))

/-- Apply `f` to every value in a machine state. -/
def State.map (f : V → W) (s : State V) : State W where
  time := s.time
  east := s.east.map (List.map (Option.map f))
  west := s.west.map (List.map (Option.map f))
  slices := s.slices.map (Slice.map f)

/-- Apply `f` to what a slice step returns. -/
def mapResult (f : V → W) (r : Slice V × Option (Stream × List V)) :
    Slice W × Option (Stream × List W) :=
  (r.1.map f, r.2.map (Prod.map id (List.map f)))

theorem State.sample_map (f : V → W) (s : State V) (p : Nat) (tr : Stream) :
    (s.map f).sample p tr = (s.sample p tr).map f := by
  unfold State.sample
  cases hd : tr.dir <;> simp only [State.belt, State.map, List.getElem?_map] <;>
    · cases (_ : List (List (Option V)))[tr.id]? with
      | none => rfl
      | some row =>
        simp only [Option.map_some, List.getElem?_map]
        cases row[p]? <;> rfl

theorem readGroup_map (f : V → W) (rd : Stream → Option V) (rd' : Stream → Option W)
    (hrd : ∀ tr, rd' tr = (rd tr).map f) (src : Stream) (g : Nat) :
    readGroup rd' src g = (readGroup rd src g).map (List.map f) := by
  induction g with
  | zero => rfl
  | succ g ih =>
    simp only [readGroup, ih, hrd]
    cases readGroup rd src g <;> cases rd (src.next g) <;> simp

theorem exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (kind : Kind) (rd : Stream → Option V) (rd' : Stream → Option W)
    (hrd : ∀ tr, rd' tr = (rd tr).map f) (sl : Slice V) (i : Instr) :
    exec T cfg kind rd' (sl.map f) i = (exec S cfg kind rd sl i).map (mapResult f) := by
  -- One case per instruction, all of the same shape: unfold `exec`, rewrite
  -- the mapped reads with `hrd` and `readGroup_map`, split on each check,
  -- then split on what each read found. Where a value is computed, `h` says
  -- `f` commutes with the operation.
  have hg := readGroup_map f rd rd' hrd
  cases i with
  | read addr dst =>
    simp only [exec, Slice.map, List.getElem?_map]
    split
    · rfl
    · split
      · rfl
      · cases sl.words[addr]? <;> rfl
  | write src addr =>
    simp only [exec, Slice.map, List.length_map, hrd]
    split
    · rfl
    · split
      · rfl
      · cases rd src <;> simp [Except.map, mapResult, Slice.map, List.map_set]
  | un ty op src dst =>
    simp only [exec, hg]
    split
    · rfl
    · split
      · rfl
      · cases readGroup rd src ty.bytes <;> simp [Except.map, mapResult, h.un]
  | bin ty op a b dst =>
    simp only [exec, hg]
    split
    · rfl
    · split
      · rfl
      · cases readGroup rd a ty.bytes <;> cases readGroup rd b ty.bytes <;>
          simp [Except.map, mapResult, h.bin]
  | const ty xs dst =>
    simp only [exec]
    split
    · rfl
    · split
      · rfl
      · simp [Except.map, mapResult, h.const]
  | sel ty m a b dst =>
    simp only [exec, hg]
    split
    · rfl
    · split
      · rfl
      · cases readGroup rd m ty.bytes <;> cases readGroup rd a ty.bytes <;>
          cases readGroup rd b ty.bytes <;> simp [Except.map, mapResult, h.sel]
  | install j g src =>
    simp only [exec, Slice.map, List.length_map, hg]
    split
    · rfl
    · split
      · rfl
      · cases readGroup rd src g <;> simp [Except.map, mapResult, Slice.map, putAt_map]
  | product n src dst =>
    simp only [exec, hrd, Slice.map, List.length_map]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · cases rd src <;> simp [Except.map, mapResult, Slice.map, h.matvec, List.map_take]

theorem slots_map (f : V → W) (sl : Slice V) (r : Option (Stream × List V)) (d : Nat) :
    (sl.map f).slots (r.map (Prod.map id (List.map f))) d =
      (sl.slots r d).map (Option.map (Prod.map id (List.map f))) := by
  cases r <;> simp [Slice.slots, Slice.map, List.map_set]

/-- Whether a result clashes depends only on which slots are full. -/
theorem clash_map (f : V → W) (sl : Slice V) (r : Option (Stream × List V)) (d : Nat) :
    (sl.map f).clash (r.map (Prod.map id (List.map f))) d = sl.clash r d := by
  simp only [Slice.clash, Slice.map, Option.isSome_map, List.length_map]
  congr 1
  rw [show (none : Option (Stream × List W)) :: sl.pipe.map (Option.map (Prod.map id (List.map f))) =
    (none :: sl.pipe).map (Option.map (Prod.map id (List.map f))) from rfl, List.getElem?_map]
  cases (none :: sl.pipe)[sl.pipe.length - d]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem shiftPipe_map (f : V → W) (sl : Slice V) (r : Option (Stream × List V)) (d : Nat) :
    shiftPipe (sl.map f) (r.map (Prod.map id (List.map f))) d = mapResult f (shiftPipe sl r d) := by
  unfold shiftPipe mapResult
  rw [slots_map]
  simp only [List.getLast?_map, Slice.map]
  refine Prod.ext ?_ ?_
  · simp
  · cases (sl.slots r d).getLast? <;> rfl

theorem execBoth_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (kind : Kind) (rd : Stream → Option V) (rd' : Stream → Option W)
    (hrd : ∀ tr, rd' tr = (rd tr).map f) (sl : Slice V) (r w : Instr) :
    execBoth T cfg kind rd' (sl.map f) r w =
      (execBoth S cfg kind rd sl r w).map (mapResult f) := by
  -- `exec_map` for the read, and then for the write on the slice it leaves.
  unfold execBoth
  rw [exec_map S T f h cfg kind rd rd' hrd sl r]
  cases exec S cfg kind rd sl r with
  | error k => rfl
  | ok a =>
    obtain ⟨sl1, res⟩ := a
    simp only [Except.map, mapResult]
    rw [exec_map S T f h cfg kind rd rd' hrd sl1 w]
    cases exec S cfg kind rd sl1 w with
    | error k => rfl
    | ok b => rfl

theorem leave_map (f : V → W) (p t d : Nat)
    (x : Except TrapKind (Slice V × Option (Stream × List V))) :
    leave p t d (x.map (mapResult f)) = (leave p t d x).map (mapResult f) := by
  cases x with
  | error k => rfl
  | ok a =>
    obtain ⟨sl, r⟩ := a
    simp only [Except.map, mapResult, leave, clash_map]
    split
    · rfl
    · exact congrArg Except.ok (shiftPipe_map f sl r d)

theorem stepSlice_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (s : State V) (p : Nat) (sl : Slice V) :
    stepSlice T cfg prog (s.map f) p (sl.map f) =
      (stepSlice S cfg prog s p sl).map (mapResult f) := by
  -- The time is the same in both states, so the same instructions are due.
  -- No instruction: `shiftPipe_map`. One: `exec_map`, then `leave_map`. A
  -- read and a write: `execBoth_map`, then `leave_map`. Otherwise the same
  -- trap on both sides.
  unfold stepSlice
  have ht : (s.map f).time = s.time := rfl
  rw [ht]
  cases prog.dueAt p s.time with
  | nil => exact congrArg Except.ok (shiftPipe_map f sl none 0)
  | cons i rest =>
    cases rest with
    | nil =>
      cases cfg.kindAt p with
      | none => rfl
      | some kind =>
        simp only
        rw [exec_map S T f h cfg kind (s.sample p) ((s.map f).sample p)
          (State.sample_map f s p) sl i]
        exact leave_map f p s.time _ _
    | cons j rest =>
      cases rest with
      | cons k rest => rfl
      | nil =>
        simp only
        cases hrw : Instr.readWrite i j with
        | none => rfl
        | some rw' =>
          obtain ⟨r, w⟩ := rw'
          cases hk : cfg.kindAt p with
          | none => rfl
          | some kind =>
            simp only
            split
            · rfl
            · rw [execBoth_map S T f h cfg kind (s.sample p) ((s.map f).sample p)
                (State.sample_map f s p) sl r w]
              exact leave_map f p s.time _ _

theorem stepSlices_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (s : State V) (p : Nat) (sls : List (Slice V)) :
    stepSlices T cfg prog (s.map f) p (sls.map (Slice.map f)) =
      (stepSlices S cfg prog s p sls).map (List.map (mapResult f)) := by
  induction sls generalizing p with
  | nil => rfl
  | cons sl rest ih =>
    simp only [List.map_cons, stepSlices, stepSlice_map S T f h, ih]
    cases stepSlice S cfg prog s p sl with
    | error e => rfl
    | ok r =>
      cases stepSlices S cfg prog s (p + 1) rest with
      | error e => rfl
      | ok rs => rfl

theorem inject_map (f : V → W) (outs : List (Option (Stream × List V))) (d : Dir) (k p : Nat) :
    inject (outs.map (Option.map (Prod.map id (List.map f)))) d k p = (inject outs d k p).map f := by
  unfold inject
  simp only [List.getElem?_map]
  cases outs[p]? with
  | none => rfl
  | some o =>
    cases o with
    | none => rfl
    | some tv =>
      obtain ⟨tr, v⟩ := tv
      simp only [Option.map_some, Option.getD_some, Prod.map, id]
      split
      · exact List.getElem?_map
      · rfl

theorem advanceRow_map (f : V → W) (outs : List (Option (Stream × List V))) (d : Dir) (k : Nat)
    (row : List (Option V)) :
    advanceRow (outs.map (Option.map (Prod.map id (List.map f)))) d k (row.map (Option.map f)) =
      (advanceRow outs d k row).map (Option.map f) := by
  unfold advanceRow
  simp only [List.length_map, List.map_map, inject_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  cases inject outs d k p with
  | some v => rfl
  | none =>
    cases d with
    | east =>
      simp only [Option.map_none, List.getElem?_map]
      split
      · rfl
      · cases row[p - 1]? <;> rfl
    | west =>
      simp only [Option.map_none, List.getElem?_map]
      cases row[p + 1]? <;> rfl

theorem advance_map (f : V → W) (outs : List (Option (Stream × List V))) (d : Dir) (k : Nat)
    (rows : List (List (Option V))) :
    advance (outs.map (Option.map (Prod.map id (List.map f)))) d k (rows.map (List.map (Option.map f))) =
      (advance outs d k rows).map (List.map (Option.map f)) := by
  induction rows generalizing k with
  | nil => rfl
  | cons row rest ih => simp only [List.map_cons, advance, advanceRow_map, ih]

/-- One cycle commutes with applying `f`. -/
theorem step_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (s : State V) :
    step T cfg prog (s.map f) = (step S cfg prog s).map (State.map f) := by
  unfold step
  have hs : (s.map f).slices = s.slices.map (Slice.map f) := rfl
  rw [hs, stepSlices_map S T f h]
  cases stepSlices S cfg prog s 0 s.slices with
  | error e => rfl
  | ok rs =>
    have h2 : (rs.map (mapResult f)).map (·.2) =
        (rs.map (·.2)).map (Option.map (Prod.map id (List.map f))) := by
      simp [List.map_map, mapResult]
    have h1 : (rs.map (mapResult f)).map (·.1) = (rs.map (·.1)).map (Slice.map f) := by
      simp [List.map_map, mapResult]
    simp only [Except.map, State.map, h1, h2, advance_map]

/-- Any number of cycles commutes with applying `f`. -/
theorem run_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (n : Nat) (s : State V) :
    run T cfg prog n (s.map f) = (run S cfg prog n s).map (State.map f) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [run, step_map S T f h]
    cases step S cfg prog s with
    | error e => rfl
    | ok s' => exact ih s'

theorem State.init_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (image : List (List V)) :
    State.init T cfg (image.map (List.map f)) = (State.init S cfg image).map f := by
  simp only [State.init, State.map, List.map_replicate, Option.map_none, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp, Slice.map, List.getElem?_map, List.map_replicate, Option.map_none,
    h.zero]
  cases image[p]? <;> rfl

theorem State.memory_map (f : V → W) (s : State V) :
    (s.map f).memory = s.memory.map (List.map f) := by
  simp [State.memory, State.map, Slice.map, List.map_map]

/-- Running a program on a mapped memory image gives the mapped result, and
traps in exactly the same cases. -/
theorem execute_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (n : Nat) (image : List (List V)) :
    execute T cfg prog n (image.map (List.map f)) =
      (execute S cfg prog n image).map (List.map (List.map f)) := by
  unfold execute
  cases prog.find? fun e => cfg.kinds.length ≤ e.slice with
  | some e => rfl
  | none =>
    simp only
    rw [State.init_map S T f h, run_map S T f h]
    cases run S cfg prog n (State.init S cfg image) with
    | error e => rfl
    | ok s => simp only [Except.map, State.memory_map]

end Tau
