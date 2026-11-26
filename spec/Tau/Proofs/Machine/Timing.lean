import Tau.Machine.Timing

/-!
# The timing rule

`Tau.Machine.SliceLevel` defines one cycle of the machine: a result enters
the pipe of its slice, the oldest entry of the pipe comes out, and every
stream moves one position. This file proves what follows from that over many
cycles. A result computed at slice `p` on cycle `t` can be read at slice `q` on
cycle `t + delay + 1 + |q - p|`.

The rule comes in three steps.

* `out_delay`: a result comes out of its slice `delay` cycles after it was
  computed.
* `sample_step`: in one cycle a word on a stream moves one position, unless
  the slice it arrives at places a result of its own in that slot.
* `arrives_east` and `arrives_west`: the two together, over any distance.

The statements are about the states of a run that does not trap (`IsRun`).
`isRun_of_run` says that every such run of the machine has them. The
definitions the statements need are in `Tau.Machine.Timing`.

Nothing else in tau-tpu depends on this file. The checker does not need the
rule, because it runs the machine itself. The rule is what a person uses to
write a schedule by hand, and what a proof about schedules would start from.

Terms to look up: *invariant*, *pipeline latency*.
-/

namespace Tau

variable {V : Type}

/-! ## One slice, one cycle -/

/-- An instruction does not touch the pipe of its slice. -/
theorem exec_pipe (S : Sem V) (cfg : Config) (kind : Kind) (rd : Stream → Option V)
    (sl sl' : Slice V) (i : Instr) (r : Option (Stream × V))
    (h : exec S cfg kind rd sl i = .ok (sl', r)) : sl'.pipe = sl.pipe := by
  cases i <;> simp only [exec] at h <;> (repeat' split at h) <;>
    first
    | contradiction
    | (cases h; rfl)

/-- A result is always meant for a stream that exists. -/
theorem exec_track (S : Sem V) (cfg : Config) (kind : Kind) (rd : Stream → Option V)
    (sl sl' : Slice V) (i : Instr) (tr : Stream) (v : V)
    (h : exec S cfg kind rd sl i = .ok (sl', some (tr, v))) : tr.id < cfg.streams := by
  cases i <;> simp only [exec] at h <;> (repeat' split at h) <;>
    first
    | contradiction
    | (cases h; omega)
    | cases h

/-- One cycle of a slice pushes its result into the pipe and takes the oldest
entry out. -/
theorem stepSlice_pipe (S : Sem V) (cfg : Config) (prog : Program) (s : State V) (p : Nat)
    (sl sl' : Slice V) (o : Option (Stream × V)) (hsl : s.slices[p]? = some sl)
    (h : stepSlice S cfg prog s p sl = .ok (sl', o)) :
    sl'.pipe = (s.result S cfg prog p :: sl.pipe).dropLast ∧
      o = (s.result S cfg prog p :: sl.pipe).getLast?.getD none := by
  -- Split on the instructions due, as `stepSlice` does. With none due the
  -- result is `none`. With one due, `exec` leaves the pipe alone
  -- (`exec_pipe`). The other cases trap.
  cases hdue : prog.dueAt p s.time with
  | nil =>
    simp only [stepSlice, hdue, shiftPipe, Except.ok.injEq, Prod.mk.injEq] at h
    simp only [State.result, hdue]
    obtain ⟨h1, h2⟩ := h
    subst h1
    exact ⟨rfl, h2.symm⟩
  | cons i rest =>
    cases rest with
    | cons j rest' => simp [stepSlice, hdue] at h
    | nil =>
      cases hk : cfg.kindAt p with
      | none => simp [stepSlice, hdue, hk] at h
      | some kind =>
        cases he : exec S cfg kind (s.sample p) sl i with
        | error k => simp [stepSlice, hdue, hk, he] at h
        | ok r =>
          obtain ⟨sl1, r1⟩ := r
          simp only [stepSlice, hdue, hk, he, shiftPipe, Except.ok.injEq, Prod.mk.injEq] at h
          simp only [State.result, hdue, hk, hsl, he]
          have hp := exec_pipe S cfg kind _ sl sl1 i r1 he
          obtain ⟨h1, h2⟩ := h
          subst h1
          rw [← hp]
          exact ⟨rfl, h2.symm⟩

/-! ## One cycle of the machine, taken apart -/

/-- If `stepSlices` does not trap, entry `i` of its answer is `stepSlice` of
entry `i` of the slices. -/
theorem stepSlices_getElem? (S : Sem V) (cfg : Config) (prog : Program) (s : State V)
    (p0 : Nat) (sls : List (Slice V)) (rs : List (Slice V × Option (Stream × V)))
    (h : stepSlices S cfg prog s p0 sls = .ok rs) (i : Nat) (sl : Slice V)
    (hsl : sls[i]? = some sl) :
    ∃ r, rs[i]? = some r ∧ stepSlice S cfg prog s (p0 + i) sl = .ok r := by
  induction sls generalizing p0 rs i with
  | nil => simp at hsl
  | cons a rest ih =>
    simp only [stepSlices] at h
    cases ha : stepSlice S cfg prog s p0 a with
    | error e => simp [ha] at h
    | ok r =>
      cases hr : stepSlices S cfg prog s (p0 + 1) rest with
      | error e => simp [ha, hr] at h
      | ok rs' =>
        simp only [ha, hr, Except.ok.injEq] at h
        subst h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hsl
          subst hsl
          exact ⟨r, rfl, ha⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hsl ⊢
          have h' := ih (p0 + 1) rs' hr i hsl
          rwa [show p0 + (i + 1) = p0 + 1 + i by omega]

/-- If `stepSlices` does not trap, it answers for every slice. -/
theorem stepSlices_length (S : Sem V) (cfg : Config) (prog : Program) (s : State V)
    (p0 : Nat) (sls : List (Slice V)) (rs : List (Slice V × Option (Stream × V)))
    (h : stepSlices S cfg prog s p0 sls = .ok rs) : rs.length = sls.length := by
  induction sls generalizing p0 rs with
  | nil =>
    simp only [stepSlices, Except.ok.injEq] at h
    subst h
    rfl
  | cons a rest ih =>
    simp only [stepSlices] at h
    cases ha : stepSlice S cfg prog s p0 a with
    | error e => simp [ha] at h
    | ok r =>
      cases hr : stepSlices S cfg prog s (p0 + 1) rest with
      | error e => simp [ha, hr] at h
      | ok rs' =>
        simp only [ha, hr, Except.ok.injEq] at h
        subst h
        simp [ih (p0 + 1) rs' hr]

/-- A cycle that does not trap: what each part of the new state is. -/
theorem step_ok (S : Sem V) (cfg : Config) (prog : Program) (s s' : State V)
    (h : step S cfg prog s = .ok s') :
    ∃ rs, stepSlices S cfg prog s 0 s.slices = .ok rs ∧
      s'.time = s.time + 1 ∧
      s'.east = advance (rs.map (·.2)) .east 0 s.east ∧
      s'.west = advance (rs.map (·.2)) .west 0 s.west ∧
      s'.slices = rs.map (·.1) := by
  unfold step at h
  cases hrs : stepSlices S cfg prog s 0 s.slices with
  | error e => simp [hrs] at h
  | ok rs =>
    simp only [hrs, Except.ok.injEq] at h
    subst h
    exact ⟨rs, rfl, rfl, rfl, rfl, rfl⟩

/-- In a cycle that does not trap, the slice at `p` took one `stepSlice`. -/
theorem step_slice (S : Sem V) (cfg : Config) (prog : Program) (s s' : State V)
    (h : step S cfg prog s = .ok s') (p : Nat) (sl : Slice V) (hsl : s.slices[p]? = some sl) :
    ∃ sl' o, s'.slices[p]? = some sl' ∧ stepSlice S cfg prog s p sl = .ok (sl', o) := by
  obtain ⟨rs, hrs, _, _, _, hslices⟩ := step_ok S cfg prog s s' h
  obtain ⟨r, hr, hstep⟩ := stepSlices_getElem? S cfg prog s 0 s.slices rs hrs p sl hsl
  rw [Nat.zero_add] at hstep
  refine ⟨r.1, r.2, ?_, hstep⟩
  rw [hslices, List.getElem?_map, hr]
  rfl

/-- The list of results that `step` hands to the streams is `State.out` at
every position. -/
theorem outs_getD (S : Sem V) (cfg : Config) (prog : Program) (s : State V)
    (rs : List (Slice V × Option (Stream × V)))
    (hrs : stepSlices S cfg prog s 0 s.slices = .ok rs) (p : Nat) :
    (rs.map (·.2))[p]?.getD none = s.out S cfg prog p := by
  cases hsl : s.slices[p]? with
  | none =>
    have hlen := stepSlices_length S cfg prog s 0 s.slices rs hrs
    have hp : rs.length ≤ p := by
      rw [hlen]
      exact List.getElem?_eq_none_iff.mp hsl
    simp [State.out, hsl, List.getElem?_eq_none hp]
  | some sl =>
    obtain ⟨r, hr, hstep⟩ := stepSlices_getElem? S cfg prog s 0 s.slices rs hrs p sl hsl
    rw [Nat.zero_add] at hstep
    simp [State.out, hsl, hstep, hr]

/-! ## The shape of the state is kept -/

/-- Stream `i` after a cycle is `advanceRow` of stream `i` before it. -/
theorem advance_getElem? (outs : List (Option (Stream × V))) (d : Dir) (id i : Nat)
    (rows : List (List (Option V))) :
    (advance outs d id rows)[i]? = (rows[i]?).map (advanceRow outs d (id + i)) := by
  induction rows generalizing id i with
  | nil => rfl
  | cons row rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [advance, List.getElem?_cons_succ]
      rw [ih (id + 1) i, show id + 1 + i = id + (i + 1) by omega]

/-- A cycle keeps the number of streams. -/
theorem advance_length (outs : List (Option (Stream × V))) (d : Dir) (id : Nat)
    (rows : List (List (Option V))) : (advance outs d id rows).length = rows.length := by
  induction rows generalizing id with
  | nil => rfl
  | cons row rest ih => simp [advance, ih]

/-- A cycle keeps the length of a stream. -/
theorem advanceRow_length (outs : List (Option (Stream × V))) (d : Dir) (id : Nat)
    (row : List (Option V)) : (advanceRow outs d id row).length = row.length := by
  simp [advanceRow]

/-- The starting state has the shape of the machine. -/
theorem State.init_shaped (S : Sem V) (cfg : Config) (image : List (List V)) :
    (State.init S cfg image).Shaped cfg where
  east := by simp [State.init]
  west := by simp [State.init]
  eastRow := by
    intro id row h
    simp only [State.init, List.getElem?_replicate] at h
    split at h
    · cases h
      simp
    · cases h
  westRow := by
    intro id row h
    simp only [State.init, List.getElem?_replicate] at h
    split at h
    · cases h
      simp
    · cases h
  slices := by simp [State.init]
  pipe := by
    intro p sl kind hsl hk
    unfold Config.kindAt at hk
    have hlt : p < cfg.kinds.length := by
      cases Nat.lt_or_ge p cfg.kinds.length with
      | inl h => exact h
      | inr h => simp [List.getElem?_eq_none h] at hk
    simp only [State.init, List.getElem?_map, List.getElem?_range hlt, Option.map_some,
      Option.some.injEq] at hsl
    subst hsl
    simp [hk]

/-- A cycle that does not trap keeps the shape. -/
theorem State.Shaped.step (S : Sem V) (cfg : Config) (prog : Program) (s s' : State V)
    (hs : s.Shaped cfg) (h : Tau.step S cfg prog s = .ok s') : s'.Shaped cfg := by
  obtain ⟨rs, hrs, _, heast, hwest, hslices⟩ := step_ok S cfg prog s s' h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heast, advance_length, hs.east]
  · rw [hwest, advance_length, hs.west]
  · intro id row hrow
    rw [heast, advance_getElem?] at hrow
    cases h0 : s.east[id]? with
    | none => simp [h0] at hrow
    | some row0 =>
      simp only [h0, Option.map_some, Option.some.injEq] at hrow
      rw [← hrow, advanceRow_length]
      exact hs.eastRow id row0 h0
  · intro id row hrow
    rw [hwest, advance_getElem?] at hrow
    cases h0 : s.west[id]? with
    | none => simp [h0] at hrow
    | some row0 =>
      simp only [h0, Option.map_some, Option.some.injEq] at hrow
      rw [← hrow, advanceRow_length]
      exact hs.westRow id row0 h0
  · rw [hslices, List.length_map, stepSlices_length S cfg prog s 0 s.slices rs hrs, hs.slices]
  · intro p sl' kind hsl' hk
    cases hsl : s.slices[p]? with
    | none =>
      have hp : rs.length ≤ p := by
        rw [stepSlices_length S cfg prog s 0 s.slices rs hrs]
        exact List.getElem?_eq_none_iff.mp hsl
      simp [hslices, List.getElem?_eq_none hp] at hsl'
    | some sl =>
      obtain ⟨sl1, o, hsl1, hstep⟩ := step_slice S cfg prog s s' h p sl hsl
      rw [hsl1, Option.some.injEq] at hsl'
      rw [← hsl', (stepSlice_pipe S cfg prog s p sl sl1 o hsl hstep).1, List.length_dropLast,
        List.length_cons, Nat.add_sub_cancel]
      exact hs.pipe p sl kind hsl hk

/-- Every state of a run from a shaped state is shaped. -/
theorem IsRun.shaped (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V) (n : Nat)
    (hrun : IsRun S cfg prog st n) (h0 : (st 0).Shaped cfg) (u : Nat) (hu : u ≤ n) :
    (st u).Shaped cfg := by
  induction u with
  | zero => exact h0
  | succ u ih => exact (ih (by omega)).step S cfg prog _ _ (hrun u (by omega))

/-- A position that has a kind is a position of the machine. -/
theorem Config.kindAt_lt (cfg : Config) (p : Nat) (kind : Kind)
    (hk : cfg.kindAt p = some kind) : p < cfg.kinds.length := by
  unfold Config.kindAt at hk
  cases Nat.lt_or_ge p cfg.kinds.length with
  | inl h => exact h
  | inr h => simp [List.getElem?_eq_none h] at hk

/-- A shaped state has a slice state at every position of the machine. -/
theorem State.Shaped.slice (cfg : Config) (s : State V) (hs : s.Shaped cfg) (p : Nat)
    (kind : Kind) (hk : cfg.kindAt p = some kind) : ∃ sl, s.slices[p]? = some sl := by
  have hlt : p < s.slices.length := by
    rw [hs.slices]
    exact cfg.kindAt_lt p kind hk
  exact ⟨s.slices[p], List.getElem?_eq_getElem hlt⟩

/-! ## Inside a slice: the delay -/

/-- A result that is `j` cycles old is at place `j` in the list that `shiftPipe`
looks at: this cycle's result, followed by the pipe. -/
theorem pipe_getElem? (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V)
    (n : Nat) (hrun : IsRun S cfg prog st n) (h0 : (st 0).Shaped cfg) (p : Nat) (kind : Kind)
    (hk : cfg.kindAt p = some kind) (t j : Nat) (hj : j ≤ cfg.delay kind) (hn : t + j ≤ n) :
    ∃ sl, (st (t + j)).slices[p]? = some sl ∧
      ((st (t + j)).result S cfg prog p :: sl.pipe)[j]? = some ((st t).result S cfg prog p) := by
  -- Induction on `j`. A new result is at the head. One cycle later the pipe
  -- is the old list without its last entry (`stepSlice_pipe`), so every
  -- entry but the last has moved one place back.
  induction j with
  | zero =>
    have hs := IsRun.shaped S cfg prog st n hrun h0 t (by omega)
    obtain ⟨sl, hsl⟩ := hs.slice cfg _ p kind hk
    exact ⟨sl, hsl, rfl⟩
  | succ j ih =>
    obtain ⟨sl, hsl, hget⟩ := ih (by omega) (by omega)
    have hs := IsRun.shaped S cfg prog st n hrun h0 (t + j) (by omega)
    have hstep := hrun (t + j) (by omega)
    obtain ⟨sl', o, hsl', hss⟩ := step_slice S cfg prog _ _ hstep p sl hsl
    refine ⟨sl', hsl', ?_⟩
    have hlen := hs.pipe p sl kind hsl hk
    have hlt : j < cfg.delay kind := by omega
    rw [List.getElem?_cons_succ, (stepSlice_pipe S cfg prog _ p sl sl' o hsl hss).1,
      List.getElem?_dropLast, List.length_cons, hlen, Nat.add_sub_cancel]
    simp only [hlt, ↓reduceIte]
    exact hget

/-- **The delay of a slice.** A result that a slice of kind `kind` computes on
cycle `t` comes out of the slice on cycle `t + delay`. -/
theorem out_delay (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V) (n : Nat)
    (hrun : IsRun S cfg prog st n) (h0 : (st 0).Shaped cfg) (p : Nat) (kind : Kind)
    (hk : cfg.kindAt p = some kind) (t : Nat) (hn : t + cfg.delay kind < n) :
    (st (t + cfg.delay kind)).out S cfg prog p = (st t).result S cfg prog p := by
  -- After `delay` cycles the result is the last entry of the list
  -- (`pipe_getElem?`), and the last entry is what comes out.
  obtain ⟨sl, hsl, hget⟩ := pipe_getElem? S cfg prog st n hrun h0 p kind hk t (cfg.delay kind)
    (Nat.le_refl _) (by omega)
  have hs := IsRun.shaped S cfg prog st n hrun h0 (t + cfg.delay kind) (by omega)
  have hstep := hrun (t + cfg.delay kind) hn
  obtain ⟨sl', o, _, hss⟩ := step_slice S cfg prog _ _ hstep p sl hsl
  have hlen := hs.pipe p sl kind hsl hk
  have ho := (stepSlice_pipe S cfg prog _ p sl sl' o hsl hss).2
  simp only [State.out, hsl, hss]
  rw [ho, List.getLast?_eq_getElem?, List.length_cons, hlen, Nat.add_sub_cancel, hget]
  rfl

/-! ## Between slices: one position per cycle -/

/-- Slot `p` of a stream after a cycle: a newly placed result if there is
one, else the word from one position upstream. -/
theorem advanceRow_getElem? (outs : List (Option (Stream × V))) (d : Dir) (id : Nat)
    (row : List (Option V)) (p : Nat) (hp : p < row.length) :
    (advanceRow outs d id row)[p]? = some
      (match inject outs d id p with
       | some v => some v
       | none =>
         match d with
         | .east => if p = 0 then none else row[p - 1]?.getD none
         | .west => row[p + 1]?.getD none) := by
  simp only [advanceRow, List.getElem?_map, List.getElem?_range hp, Option.map_some]
  cases inject outs d id p <;> cases d <;> rfl

/-- **One cycle of a stream.** After a cycle, the slot of stream `tr` at
position `p` holds the word that the slice at `p` placed on `tr` in that
cycle, if it placed one. Otherwise it holds what was one position upstream. -/
theorem sample_step (S : Sem V) (cfg : Config) (prog : Program) (s s' : State V)
    (hs : s.Shaped cfg) (h : step S cfg prog s = .ok s') (p : Nat) (tr : Stream)
    (hp : p < cfg.kinds.length) (hid : tr.id < cfg.streams) :
    s'.sample p tr =
      match s.out S cfg prog p with
      | some (tr', v) => if tr' = tr then some v else s.upstream p tr
      | none => s.upstream p tr := by
  -- The new streams are `advance` of the old ones (`step_ok`). Find the row
  -- of `tr` before the cycle, read slot `p` of the advanced row
  -- (`advanceRow_getElem?`), and compare the two sides case by case.
  obtain ⟨rs, hrs, _, heast, hwest, _⟩ := step_ok S cfg prog s s' h
  have hbelt : s'.belt tr.dir = advance (rs.map (·.2)) tr.dir 0 (s.belt tr.dir) := by
    cases tr.dir
    · exact heast
    · exact hwest
  have hrow : ∃ row, (s.belt tr.dir)[tr.id]? = some row ∧ row.length = cfg.kinds.length := by
    cases tr.dir with
    | east =>
      have hlt : tr.id < s.east.length := by rw [hs.east]; exact hid
      exact ⟨s.east[tr.id], List.getElem?_eq_getElem hlt,
        hs.eastRow _ _ (List.getElem?_eq_getElem hlt)⟩
    | west =>
      have hlt : tr.id < s.west.length := by rw [hs.west]; exact hid
      exact ⟨s.west[tr.id], List.getElem?_eq_getElem hlt,
        hs.westRow _ _ (List.getElem?_eq_getElem hlt)⟩
  obtain ⟨row, hrow, hlen⟩ := hrow
  have hsample : ∀ q, s.sample q tr = row[q]?.getD none := by
    intro q
    simp only [State.sample, hrow]
  simp only [State.sample, hbelt, advance_getElem?, hrow, Option.map_some, Nat.zero_add]
  rw [advanceRow_getElem? _ _ _ _ _ (by omega)]
  simp only [Option.getD_some, inject, outs_getD S cfg prog s rs hrs p]
  cases ho : s.out S cfg prog p with
  | none =>
    simp only [State.upstream, hsample]
    cases tr.dir <;> rfl
  | some r =>
    obtain ⟨tr', v⟩ := r
    by_cases heq : tr' = tr
    · subst heq
      simp
    · have hne : ¬ (tr'.dir = tr.dir ∧ tr'.id = tr.id) := by
        intro hand
        apply heq
        cases tr'
        cases tr
        simp_all
      simp only [hne, heq, ↓reduceIte, State.upstream, hsample]
      cases tr.dir <;> rfl

/-! ## The timing rule -/

/-- A result is always meant for a stream that exists. -/
theorem State.result_track (S : Sem V) (cfg : Config) (prog : Program) (s : State V) (p : Nat)
    (tr : Stream) (v : V) (h : s.result S cfg prog p = some (tr, v)) : tr.id < cfg.streams := by
  cases hdue : prog.dueAt p s.time with
  | nil => simp [State.result, hdue] at h
  | cons i rest =>
    cases rest with
    | cons j rest' => simp [State.result, hdue] at h
    | nil =>
      cases hk : cfg.kindAt p with
      | none => simp [State.result, hdue, hk] at h
      | some kind =>
        cases hsl : s.slices[p]? with
        | none => simp [State.result, hdue, hk, hsl] at h
        | some sl =>
          cases he : exec S cfg kind (s.sample p) sl i with
          | error e => simp [State.result, hdue, hk, hsl, he] at h
          | ok r =>
            obtain ⟨sl', r'⟩ := r
            simp only [State.result, hdue, hk, hsl, he] at h
            subst h
            exact exec_track S cfg kind _ sl sl' i tr v he

/-- **The timing rule, going east.** Suppose the slice at `p`, of kind `kind`,
computes the word `v` on cycle `t` for the stream `id` going east, and no
slice between `p + 1` and `p + k` places a word of its own on that stream
just as `v` arrives there. Then on cycle `t + delay + 1 + k` the slice at
`p + k` finds `v` in the slot of that stream. -/
theorem arrives_east (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V) (n : Nat)
    (hrun : IsRun S cfg prog st n) (h0 : (st 0).Shaped cfg) (p t id : Nat) (kind : Kind)
    (v : V) (hk : cfg.kindAt p = some kind)
    (hres : (st t).result S cfg prog p = some (⟨.east, id⟩, v)) (k : Nat)
    (hq : p + k < cfg.kinds.length) (hn : t + cfg.delay kind + 1 + k ≤ n)
    (hfree : ∀ i, 1 ≤ i → i ≤ k → ∀ w,
      (st (t + cfg.delay kind + i)).out S cfg prog (p + i) ≠ some (⟨.east, id⟩, w)) :
    (st (t + cfg.delay kind + 1 + k)).sample (p + k) ⟨.east, id⟩ = some v := by
  -- Induction on the distance `k`. At distance 0 the word comes out of the
  -- slice after `delay` cycles (`out_delay`) and is on the stream one cycle
  -- later (`sample_step`). Each further position costs one more cycle
  -- (`sample_step` again, with nothing placed in the way).
  have hid : id < cfg.streams := State.result_track S cfg prog _ p _ v hres
  induction k with
  | zero =>
    have hout := out_delay S cfg prog st n hrun h0 p kind hk t (by omega)
    rw [hres] at hout
    have hs := IsRun.shaped S cfg prog st n hrun h0 (t + cfg.delay kind) (by omega)
    have hstep := hrun (t + cfg.delay kind) (by omega)
    have h1 := sample_step S cfg prog _ _ hs hstep p ⟨.east, id⟩ (by omega) hid
    rw [hout] at h1
    simpa using h1
  | succ k ih =>
    have ih' := ih (by omega) (by omega) (fun i hi1 hi2 => hfree i hi1 (by omega))
    have hs := IsRun.shaped S cfg prog st n hrun h0 (t + cfg.delay kind + 1 + k) (by omega)
    have hstep := hrun (t + cfg.delay kind + 1 + k) (by omega)
    have h1 := sample_step S cfg prog _ _ hs hstep (p + (k + 1)) ⟨.east, id⟩ hq hid
    have hfr := hfree (k + 1) (by omega) (Nat.le_refl _)
    rw [show t + cfg.delay kind + (k + 1) = t + cfg.delay kind + 1 + k by omega] at hfr
    have hup : (st (t + cfg.delay kind + 1 + k)).upstream (p + (k + 1)) ⟨.east, id⟩ = some v := by
      have hne0 : p + (k + 1) ≠ 0 := by omega
      simp only [State.upstream, hne0, ↓reduceIte]
      rw [show p + (k + 1) - 1 = p + k by omega]
      exact ih'
    cases ho : (st (t + cfg.delay kind + 1 + k)).out S cfg prog (p + (k + 1)) with
    | none =>
      rw [ho] at h1
      exact h1.trans hup
    | some r =>
      obtain ⟨tr', w⟩ := r
      by_cases heq : tr' = ⟨.east, id⟩
      · subst heq
        exact absurd ho (hfr w)
      · rw [ho] at h1
        simp only [heq, ↓reduceIte] at h1
        exact h1.trans hup

/-- **The timing rule, going west.** The mirror image of `arrives_east`: a
word computed at `p` on cycle `t` for a stream going west is at `p - k` on
cycle `t + delay + 1 + k`. -/
theorem arrives_west (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V) (n : Nat)
    (hrun : IsRun S cfg prog st n) (h0 : (st 0).Shaped cfg) (p t id : Nat) (kind : Kind)
    (v : V) (hk : cfg.kindAt p = some kind)
    (hres : (st t).result S cfg prog p = some (⟨.west, id⟩, v)) (k : Nat)
    (hq : k ≤ p) (hn : t + cfg.delay kind + 1 + k ≤ n)
    (hfree : ∀ i, 1 ≤ i → i ≤ k → ∀ w,
      (st (t + cfg.delay kind + i)).out S cfg prog (p - i) ≠ some (⟨.west, id⟩, w)) :
    (st (t + cfg.delay kind + 1 + k)).sample (p - k) ⟨.west, id⟩ = some v := by
  -- As `arrives_east`, with positions going down.
  have hid : id < cfg.streams := State.result_track S cfg prog _ p _ v hres
  have hp := cfg.kindAt_lt p kind hk
  induction k with
  | zero =>
    have hout := out_delay S cfg prog st n hrun h0 p kind hk t (by omega)
    rw [hres] at hout
    have hs := IsRun.shaped S cfg prog st n hrun h0 (t + cfg.delay kind) (by omega)
    have hstep := hrun (t + cfg.delay kind) (by omega)
    have h1 := sample_step S cfg prog _ _ hs hstep p ⟨.west, id⟩ hp hid
    rw [hout] at h1
    simpa using h1
  | succ k ih =>
    have ih' := ih (by omega) (by omega) (fun i hi1 hi2 => hfree i hi1 (by omega))
    have hs := IsRun.shaped S cfg prog st n hrun h0 (t + cfg.delay kind + 1 + k) (by omega)
    have hstep := hrun (t + cfg.delay kind + 1 + k) (by omega)
    have h1 := sample_step S cfg prog _ _ hs hstep (p - (k + 1)) ⟨.west, id⟩ (by omega) hid
    have hfr := hfree (k + 1) (by omega) (Nat.le_refl _)
    rw [show t + cfg.delay kind + (k + 1) = t + cfg.delay kind + 1 + k by omega] at hfr
    have hup : (st (t + cfg.delay kind + 1 + k)).upstream (p - (k + 1)) ⟨.west, id⟩ = some v := by
      simp only [State.upstream]
      rw [show p - (k + 1) + 1 = p - k by omega]
      exact ih'
    cases ho : (st (t + cfg.delay kind + 1 + k)).out S cfg prog (p - (k + 1)) with
    | none =>
      rw [ho] at h1
      exact h1.trans hup
    | some r =>
      obtain ⟨tr', w⟩ := r
      by_cases heq : tr' = ⟨.west, id⟩
      · subst heq
        exact absurd ho (hfr w)
      · rw [ho] at h1
        simp only [heq, ↓reduceIte] at h1
        exact h1.trans hup

/-! ## Runs exist -/

/-- A run of the machine that does not trap has states in the sense of
`IsRun`, so the theorems above apply to it. -/
theorem isRun_of_run (S : Sem V) (cfg : Config) (prog : Program) (n : Nat) (s s' : State V)
    (h : run S cfg prog n s = .ok s') :
    ∃ st, st 0 = s ∧ st n = s' ∧ IsRun S cfg prog st n := by
  induction n generalizing s with
  | zero =>
    simp only [run, Except.ok.injEq] at h
    exact ⟨fun _ => s, rfl, h, fun u hu => absurd hu (Nat.not_lt_zero u)⟩
  | succ n ih =>
    simp only [run] at h
    cases hstep : step S cfg prog s with
    | error e => simp [hstep] at h
    | ok s1 =>
      simp only [hstep] at h
      obtain ⟨st1, h10, h1n, hrun1⟩ := ih s1 h
      refine ⟨fun u => match u with | 0 => s | u + 1 => st1 u, rfl, h1n, ?_⟩
      intro u hu
      cases u with
      | zero => simpa [h10] using hstep
      | succ u => exact hrun1 u (by omega)

end Tau
