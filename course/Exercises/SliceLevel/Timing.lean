/-
Exercise file. Generated from Tau/Proofs/SliceLevel/Timing.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/SliceLevel/Timing.lean.
Build this file alone with:

    lake build Exercises.SliceLevel.Timing
-/

import Tau.SliceLevel.Machine

/-!
# The timing rule

`Tau/SliceLevel/Machine.lean` defines one cycle of the machine: a result enters
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
`isRun_of_run` says that every such run of the machine has them.

Nothing else in tau-tpu depends on this file. The checker does not need the
rule, because it runs the machine itself. The rule is what a person uses to
write a schedule by hand, and what a proof about schedules would start from.

Terms to look up: *invariant*, *pipeline latency*.
-/

namespace Tau

variable {V : Type}

/-- The states of a run of `n` cycles that does not trap: `st u` is the state
at the start of cycle `u`. -/
def IsRun (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V) (n : Nat) : Prop :=
  ∀ u, u < n → step S cfg prog (st u) = .ok (st (u + 1))

/-- A state has the shape of the chip: the right number of streams, every
stream as long as the row of slices, one slice state per position, and in
every slice a pipe as long as the delay of its kind. -/
structure State.Shaped (cfg : Config) (s : State V) : Prop where
  /-- There are `cfg.streams` streams going east. -/
  east : s.east.length = cfg.streams
  /-- There are `cfg.streams` streams going west. -/
  west : s.west.length = cfg.streams
  /-- Every stream going east has one slot per slice. -/
  eastRow : ∀ (id : Nat) (row : List (Option V)),
    s.east[id]? = some row → row.length = cfg.kinds.length
  /-- Every stream going west has one slot per slice. -/
  westRow : ∀ (id : Nat) (row : List (Option V)),
    s.west[id]? = some row → row.length = cfg.kinds.length
  /-- There is one slice state per position. -/
  slices : s.slices.length = cfg.kinds.length
  /-- The pipe of every slice is as long as the delay of its kind. -/
  pipe : ∀ (p : Nat) (sl : Slice V) (kind : Kind),
    s.slices[p]? = some sl → cfg.kindAt p = some kind → sl.pipe.length = cfg.delay kind

/-- The result that the slice at `p` computes in the cycle that starts in
`s`, with the stream it is meant for. This is what `exec` returns, before the
result enters the pipe. `none` if no instruction is due or the instruction
has no result. -/
def State.result (S : Sem V) (cfg : Config) (prog : Program) (s : State V) (p : Nat) :
    Option (Track × V) :=
  match prog.dueAt p s.time, cfg.kindAt p, s.slices[p]? with
  | [i], some kind, some sl =>
    match exec S cfg kind (s.sample p) sl i with
    | .ok (_, r) => r
    | .error _ => none
  | _, _, _ => none

/-- What comes out of the pipe of the slice at `p` in the cycle that starts in
`s`. This is the result that the machine places on a stream at position `p`. -/
def State.out (S : Sem V) (cfg : Config) (prog : Program) (s : State V) (p : Nat) :
    Option (Track × V) :=
  match s.slices[p]? with
  | some sl =>
    match stepSlice S cfg prog s p sl with
    | .ok (_, o) => o
    | .error _ => none
  | none => none

/-- What stream `tr` holds one position upstream of `p`. This is the word
that reaches `p` on the next cycle, if no slice places a result there. -/
def State.upstream (s : State V) (p : Nat) (tr : Track) : Option V :=
  match tr.dir with
  | .east => if p = 0 then none else s.sample (p - 1) tr
  | .west => s.sample (p + 1) tr

/-! ## One slice, one cycle -/

/-- An instruction does not touch the pipe of its slice. -/
theorem exec_pipe (S : Sem V) (cfg : Config) (kind : Kind) (rd : Track → Option V)
    (sl sl' : Slice V) (i : Instr) (r : Option (Track × V))
    (h : exec S cfg kind rd sl i = .ok (sl', r)) : sl'.pipe = sl.pipe := by
  sorry

/-- A result is always meant for a stream that exists. -/
theorem exec_track (S : Sem V) (cfg : Config) (kind : Kind) (rd : Track → Option V)
    (sl sl' : Slice V) (i : Instr) (tr : Track) (v : V)
    (h : exec S cfg kind rd sl i = .ok (sl', some (tr, v))) : tr.id < cfg.streams := by
  sorry

/-- One cycle of a slice pushes its result into the pipe and takes the oldest
entry out. -/
theorem stepSlice_pipe (S : Sem V) (cfg : Config) (prog : Program) (s : State V) (p : Nat)
    (sl sl' : Slice V) (o : Option (Track × V)) (hsl : s.slices[p]? = some sl)
    (h : stepSlice S cfg prog s p sl = .ok (sl', o)) :
    sl'.pipe = (s.result S cfg prog p :: sl.pipe).dropLast ∧
      o = (s.result S cfg prog p :: sl.pipe).getLast?.getD none := by
  -- Outline of one proof:
  -- Split on the instructions due, as `stepSlice` does. With none due the
  -- result is `none`. With one due, `exec` leaves the pipe alone
  -- (`exec_pipe`). The other cases trap.
  sorry

/-! ## One cycle of the machine, taken apart -/

/-- If `stepSlices` does not trap, entry `i` of its answer is `stepSlice` of
entry `i` of the slices. -/
theorem stepSlices_getElem? (S : Sem V) (cfg : Config) (prog : Program) (s : State V)
    (p0 : Nat) (sls : List (Slice V)) (rs : List (Slice V × Option (Track × V)))
    (h : stepSlices S cfg prog s p0 sls = .ok rs) (i : Nat) (sl : Slice V)
    (hsl : sls[i]? = some sl) :
    ∃ r, rs[i]? = some r ∧ stepSlice S cfg prog s (p0 + i) sl = .ok r := by
  sorry

/-- If `stepSlices` does not trap, it answers for every slice. -/
theorem stepSlices_length (S : Sem V) (cfg : Config) (prog : Program) (s : State V)
    (p0 : Nat) (sls : List (Slice V)) (rs : List (Slice V × Option (Track × V)))
    (h : stepSlices S cfg prog s p0 sls = .ok rs) : rs.length = sls.length := by
  sorry

/-- A cycle that does not trap: what each part of the new state is. -/
theorem step_ok (S : Sem V) (cfg : Config) (prog : Program) (s s' : State V)
    (h : step S cfg prog s = .ok s') :
    ∃ rs, stepSlices S cfg prog s 0 s.slices = .ok rs ∧
      s'.time = s.time + 1 ∧
      s'.east = advance (rs.map (·.2)) .east 0 s.east ∧
      s'.west = advance (rs.map (·.2)) .west 0 s.west ∧
      s'.slices = rs.map (·.1) := by
  sorry

/-- In a cycle that does not trap, the slice at `p` took one `stepSlice`. -/
theorem step_slice (S : Sem V) (cfg : Config) (prog : Program) (s s' : State V)
    (h : step S cfg prog s = .ok s') (p : Nat) (sl : Slice V) (hsl : s.slices[p]? = some sl) :
    ∃ sl' o, s'.slices[p]? = some sl' ∧ stepSlice S cfg prog s p sl = .ok (sl', o) := by
  sorry

/-- The list of results that `step` hands to the streams is `State.out` at
every position. -/
theorem outs_getD (S : Sem V) (cfg : Config) (prog : Program) (s : State V)
    (rs : List (Slice V × Option (Track × V)))
    (hrs : stepSlices S cfg prog s 0 s.slices = .ok rs) (p : Nat) :
    (rs.map (·.2))[p]?.getD none = s.out S cfg prog p := by
  sorry

/-! ## The shape of the state is kept -/

/-- Stream `i` after a cycle is `advanceRow` of stream `i` before it. -/
theorem advance_getElem? (outs : List (Option (Track × V))) (d : Dir) (id i : Nat)
    (rows : List (List (Option V))) :
    (advance outs d id rows)[i]? = (rows[i]?).map (advanceRow outs d (id + i)) := by
  sorry

/-- A cycle keeps the number of streams. -/
theorem advance_length (outs : List (Option (Track × V))) (d : Dir) (id : Nat)
    (rows : List (List (Option V))) : (advance outs d id rows).length = rows.length := by
  sorry

/-- A cycle keeps the length of a stream. -/
theorem advanceRow_length (outs : List (Option (Track × V))) (d : Dir) (id : Nat)
    (row : List (Option V)) : (advanceRow outs d id row).length = row.length := by
  sorry

/-- The starting state has the shape of the chip. -/
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
  sorry

/-- Every state of a run from a shaped state is shaped. -/
theorem IsRun.shaped (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V) (n : Nat)
    (hrun : IsRun S cfg prog st n) (h0 : (st 0).Shaped cfg) (u : Nat) (hu : u ≤ n) :
    (st u).Shaped cfg := by
  sorry

/-- A position that has a kind is a position of the chip. -/
theorem Config.kindAt_lt (cfg : Config) (p : Nat) (kind : Kind)
    (hk : cfg.kindAt p = some kind) : p < cfg.kinds.length := by
  sorry

/-- A shaped state has a slice state at every position of the chip. -/
theorem State.Shaped.slice (cfg : Config) (s : State V) (hs : s.Shaped cfg) (p : Nat)
    (kind : Kind) (hk : cfg.kindAt p = some kind) : ∃ sl, s.slices[p]? = some sl := by
  sorry

/-! ## Inside a slice: the delay -/

/-- A result that is `j` cycles old is at place `j` in the list that `shiftPipe`
looks at: this cycle's result, followed by the pipe. -/
theorem pipe_getElem? (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V)
    (n : Nat) (hrun : IsRun S cfg prog st n) (h0 : (st 0).Shaped cfg) (p : Nat) (kind : Kind)
    (hk : cfg.kindAt p = some kind) (t j : Nat) (hj : j ≤ cfg.delay kind) (hn : t + j ≤ n) :
    ∃ sl, (st (t + j)).slices[p]? = some sl ∧
      ((st (t + j)).result S cfg prog p :: sl.pipe)[j]? = some ((st t).result S cfg prog p) := by
  -- Outline of one proof:
  -- Induction on `j`. A new result is at the head. One cycle later the pipe
  -- is the old list without its last entry (`stepSlice_pipe`), so every
  -- entry but the last has moved one place back.
  sorry

/-- **The delay of a slice.** A result that a slice of kind `kind` computes on
cycle `t` comes out of the slice on cycle `t + delay`. -/
theorem out_delay (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V) (n : Nat)
    (hrun : IsRun S cfg prog st n) (h0 : (st 0).Shaped cfg) (p : Nat) (kind : Kind)
    (hk : cfg.kindAt p = some kind) (t : Nat) (hn : t + cfg.delay kind < n) :
    (st (t + cfg.delay kind)).out S cfg prog p = (st t).result S cfg prog p := by
  -- Outline of one proof:
  -- After `delay` cycles the result is the last entry of the list
  -- (`pipe_getElem?`), and the last entry is what comes out.
  sorry

/-! ## Between slices: one position per cycle -/

/-- Slot `p` of a stream after a cycle: a newly placed result if there is
one, else the word from one position upstream. -/
theorem advanceRow_getElem? (outs : List (Option (Track × V))) (d : Dir) (id : Nat)
    (row : List (Option V)) (p : Nat) (hp : p < row.length) :
    (advanceRow outs d id row)[p]? = some
      (match inject outs d id p with
       | some v => some v
       | none =>
         match d with
         | .east => if p = 0 then none else row[p - 1]?.getD none
         | .west => row[p + 1]?.getD none) := by
  sorry

/-- **One cycle of a stream.** After a cycle, the slot of stream `tr` at
position `p` holds the word that the slice at `p` placed on `tr` in that
cycle, if it placed one. Otherwise it holds what was one position upstream. -/
theorem sample_step (S : Sem V) (cfg : Config) (prog : Program) (s s' : State V)
    (hs : s.Shaped cfg) (h : step S cfg prog s = .ok s') (p : Nat) (tr : Track)
    (hp : p < cfg.kinds.length) (hid : tr.id < cfg.streams) :
    s'.sample p tr =
      match s.out S cfg prog p with
      | some (tr', v) => if tr' = tr then some v else s.upstream p tr
      | none => s.upstream p tr := by
  -- Outline of one proof:
  -- The new streams are `advance` of the old ones (`step_ok`). Find the row
  -- of `tr` before the cycle, read slot `p` of the advanced row
  -- (`advanceRow_getElem?`), and compare the two sides case by case.
  sorry

/-! ## The timing rule -/

/-- A result is always meant for a stream that exists. -/
theorem State.result_track (S : Sem V) (cfg : Config) (prog : Program) (s : State V) (p : Nat)
    (tr : Track) (v : V) (h : s.result S cfg prog p = some (tr, v)) : tr.id < cfg.streams := by
  sorry

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
  -- Outline of one proof:
  -- Induction on the distance `k`. At distance 0 the word comes out of the
  -- slice after `delay` cycles (`out_delay`) and is on the stream one cycle
  -- later (`sample_step`). Each further position costs one more cycle
  -- (`sample_step` again, with nothing placed in the way).
  sorry

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
  -- Outline of one proof:
  -- As `arrives_east`, with positions going down.
  sorry

/-! ## Runs exist -/

/-- A run of the machine that does not trap has states in the sense of
`IsRun`, so the theorems above apply to it. -/
theorem isRun_of_run (S : Sem V) (cfg : Config) (prog : Program) (n : Nat) (s s' : State V)
    (h : run S cfg prog n s = .ok s') :
    ∃ st, st 0 = s ∧ st n = s' ∧ IsRun S cfg prog st n := by
  sorry

end Tau
