import Tau.SliceLevel.Machine

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
  x := sl.x.map f
  acc := f sl.acc
  weights := sl.weights.map f
  pipe := sl.pipe.map (Option.map (Prod.map id f))

/-- Apply `f` to every value in a machine state. -/
def State.map (f : V → W) (s : State V) : State W where
  time := s.time
  east := s.east.map (List.map (Option.map f))
  west := s.west.map (List.map (Option.map f))
  slices := s.slices.map (Slice.map f)

/-- Apply `f` to what a slice step returns. -/
def mapResult (f : V → W) (r : Slice V × Option (Track × V)) :
    Slice W × Option (Track × W) :=
  (r.1.map f, r.2.map (Prod.map id f))

theorem State.sample_map (f : V → W) (s : State V) (p : Nat) (tr : Track) :
    (s.map f).sample p tr = (s.sample p tr).map f := by
  unfold State.sample
  cases hd : tr.dir <;> simp only [State.belt, State.map, List.getElem?_map] <;>
    · cases (_ : List (List (Option V)))[tr.id]? with
      | none => rfl
      | some row =>
        simp only [Option.map_some, List.getElem?_map]
        cases row[p]? <;> rfl

theorem exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (kind : Kind) (rd : Track → Option V) (rd' : Track → Option W)
    (hrd : ∀ tr, rd' tr = (rd tr).map f) (sl : Slice V) (i : Instr) :
    exec T cfg kind rd' (sl.map f) i = (exec S cfg kind rd sl i).map (mapResult f) := by
  -- One case per instruction, all of the same shape: unfold `exec`, rewrite
  -- the mapped reads with `hrd`, split on each check, then split on what
  -- each read found. Where a value is computed, `h` says `f` commutes with
  -- the operation.
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
  | un op src dst =>
    simp only [exec, hrd]
    split
    · rfl
    · split
      · rfl
      · cases rd src <;> simp [Except.map, mapResult, h.un]
  | bin op a b dst =>
    simp only [exec, hrd]
    split
    · rfl
    · split
      · rfl
      · cases rd a <;> cases rd b <;> simp [Except.map, mapResult, h.bin]
  | load src =>
    simp only [exec, hrd]
    split
    · rfl
    · cases rd src <;> simp [Except.map, mapResult, Slice.map]
  | mac j src =>
    simp only [exec, hrd, Slice.map]
    split
    · rfl
    · cases sl.x <;> cases rd src <;> simp [Except.map, mapResult, Slice.map, h.mac]
  | emit dst =>
    simp only [exec]
    split
    · rfl
    · split
      · rfl
      · simp [Except.map, mapResult, Slice.map, h.zero]
  | const xs dst =>
    simp only [exec]
    split
    · rfl
    · split
      · rfl
      · simp [Except.map, mapResult, h.const]
  | sel m a b dst =>
    simp only [exec, hrd]
    split
    · rfl
    · split
      · rfl
      · cases rd m <;> cases rd a <;> cases rd b <;> simp [Except.map, mapResult, h.sel]
  | seed src =>
    simp only [exec, hrd]
    split
    · rfl
    · cases rd src <;> simp [Except.map, mapResult, Slice.map]
  | install j src =>
    simp only [exec, hrd, Slice.map, List.length_map]
    split
    · rfl
    · split
      · rfl
      · cases rd src <;> simp [Except.map, mapResult, Slice.map, List.map_set]
  | macw j =>
    simp only [exec, Slice.map, List.getElem?_map]
    split
    · rfl
    · cases sl.x <;> cases sl.weights[j]? <;> simp [Except.map, mapResult, Slice.map, h.mac]

theorem shiftPipe_map (f : V → W) (sl : Slice V) (r : Option (Track × V)) :
    shiftPipe (sl.map f) (r.map (Prod.map id f)) = mapResult f (shiftPipe sl r) := by
  have hcons : r.map (Prod.map id f) :: (sl.map f).pipe =
      (r :: sl.pipe).map (Option.map (Prod.map id f)) := rfl
  unfold shiftPipe mapResult
  rw [hcons]
  simp only [List.getLast?_map, Slice.map]
  refine Prod.ext ?_ ?_
  · simp
  · cases (r :: sl.pipe).getLast? <;> rfl

theorem stepSlice_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (s : State V) (p : Nat) (sl : Slice V) :
    stepSlice T cfg prog (s.map f) p (sl.map f) =
      (stepSlice S cfg prog s p sl).map (mapResult f) := by
  -- The time is the same in both states, so the same instructions are due.
  -- No instruction: `shiftPipe_map`. One: `exec_map`, then `shiftPipe_map`.
  -- Two or more: the same trap on both sides.
  unfold stepSlice
  have ht : (s.map f).time = s.time := rfl
  rw [ht]
  cases prog.dueAt p s.time with
  | nil => exact congrArg Except.ok (shiftPipe_map f sl none)
  | cons i rest =>
    cases rest with
    | cons j rest => rfl
    | nil =>
      cases cfg.kindAt p with
      | none => rfl
      | some kind =>
        simp only
        rw [exec_map S T f h cfg kind (s.sample p) ((s.map f).sample p)
          (State.sample_map f s p) sl i]
        cases exec S cfg kind (s.sample p) sl i with
        | error k => rfl
        | ok r =>
          obtain ⟨sl', r⟩ := r
          exact congrArg Except.ok (shiftPipe_map f sl' r)

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

theorem inject_map (f : V → W) (outs : List (Option (Track × V))) (d : Dir) (k p : Nat) :
    inject (outs.map (Option.map (Prod.map id f))) d k p = (inject outs d k p).map f := by
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
      split <;> rfl

theorem advanceRow_map (f : V → W) (outs : List (Option (Track × V))) (d : Dir) (k : Nat)
    (row : List (Option V)) :
    advanceRow (outs.map (Option.map (Prod.map id f))) d k (row.map (Option.map f)) =
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

theorem advance_map (f : V → W) (outs : List (Option (Track × V))) (d : Dir) (k : Nat)
    (rows : List (List (Option V))) :
    advance (outs.map (Option.map (Prod.map id f))) d k (rows.map (List.map (Option.map f))) =
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
        (rs.map (·.2)).map (Option.map (Prod.map id f)) := by
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
