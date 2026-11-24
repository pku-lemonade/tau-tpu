import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Tactic reference" =>
A checked example of each tactic the course uses. Put the cursor after each
line of a proof to see what the tactic did.

# Closing a goal

`rfl`: both sides compute to the same thing.

```lean
example : 2 + 2 = 4 := rfl
```

`decide`: the statement is a concrete, finite check.

```lean
example : [1, 2, 3].map (· * 2) = [2, 4, 6] := by decide
```

`exact`: here is the proof term.

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  exact ⟨hp, hq⟩
```

`omega`: arithmetic on natural numbers and integers with addition,
subtraction, comparison and constants. It reads the hypotheses too.

```lean
example (i n : Nat) (h : i + 1 < n) : i < n := by omega
```

`bv_decide`: a fact about fixed-width bit vectors, decided by a SAT solver.

```lean
example (x : BitVec 8) : x &&& x = x := by bv_decide
```

# Changing a goal

`rw [h]`: replace the left side of the equation `h` by its right side,
everywhere in the goal. `rw [← h]` goes the other way.

```lean
example (a b : Nat) (h : a = b) : b = a := by rw [h]
```

`simp`: rewrite with a large set of library lemmas until nothing more
applies. `simp [foo, h]` adds the definition `foo` and the fact `h`.
`simp only [...]` uses only what you list. `simp at h` works on a hypothesis.

```lean
example (xs : List Nat) : (xs ++ []).length = xs.length := by simp
```

`unfold name`: replace a definition by its body. `unfold name at h` does so
in the hypothesis `h`. Most tactics that change the goal accept `at h`.

```lean
example : sumTo 0 (fun k => k + 5) 1 = 0 + 5 := by
  unfold sumTo
  unfold sumTo
  rfl

example (a b : Nat) (h : a + 0 = b) : a = b := by
  simp at h
  exact h
```

`simp only [h, ↓reduceIte]`: `↓reduceIte` asks `simp` to decide an `if` whose
condition it can settle. `↓reduceDIte` is the same for `if h : ...`. You will
see both in the solutions; plain `simp [h]` does the same without being asked.

```lean
example (c : Bool) (a b : Nat) (h : c = true) : (if c then a else b) = a := by
  simp only [h, ↓reduceIte]
```

`simp_all`: simplify the goal and every hypothesis, using each to simplify
the others.

```lean
example (a b : Nat) (h1 : a = 0) (h2 : b = a) : b = 0 := by simp_all
```

`subst h`: when `h : a = b` and one side is a variable, replace that variable
everywhere and drop `h`.

```lean
example (a b : Nat) (f : Nat → Nat) (h : a = b) : f a = f b := by
  subst h
  rfl
```

`funext x`: to prove two functions equal, prove they agree on every `x`.

```lean
example : (fun n : Nat => n + 0) = (fun n => n) := by
  funext n
  simp
```

`congr 1`: to prove `f a b = f a' b'`, prove `a = a'` and `b = b'`. Goals
that are true by `rfl` are closed at once.

```lean
example (a b c : Nat) (h : b = c) : a + b = a + c := by
  congr 1
```

`congrArg f h`: a term, not a tactic. From `h : a = b` it gives
`f a = f b`.

```lean
example (a b : Nat) (h : a = b) : some a = some b := congrArg some h
```

`apply List.map_congr_left`: to prove two maps over the same list equal,
prove the two functions agree on each element of the list.

```lean
example (xs : List Nat) : xs.map (fun x => x + 0) = xs.map (fun x => x) := by
  apply List.map_congr_left
  intro x _
  simp
```

# Splitting into cases

`induction n with`: one case for zero, one for `n + 1` with a hypothesis
about `n`. Add `generalizing m` when the statement for `n + 1` needs the
hypothesis at a different `m`.

```lean
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => omega
```

`cases x with`: one case for each constructor of the type of `x`.
`cases h : e` also records which case you are in as `h`.

```lean
example (b : Bool) : (b && true) = b := by cases b <;> rfl
```

`split`: one case for each branch of an `if` or `match` in the goal.

```lean
example (n : Nat) : (if n = 0 then 1 else n) > 0 := by
  split
  · omega
  · omega
```

`by_cases h : p`: one case where `p` holds and one where it does not.

```lean
example (n : Nat) : n = 0 ∨ n > 0 := by
  by_cases h : n = 0
  · exact Or.inl h
  · exact Or.inr (by omega)
```

`rename_i k`: give a name to a variable or hypothesis that `split` or
`cases` introduced without one. Names go to the nameless items, most recent
last.

```lean
example (n : Nat) : (match n with | 0 => 1 | k + 1 => k + 2) > 0 := by
  split
  · omega
  · rename_i k
    omega
```

`t1 <;> t2` runs `t2` on every goal that `t1` produces. A `·` starts the proof
of one case.

# Intermediate facts

`have h : statement := by ...`: prove a fact and name it.

```lean
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  have h : a = c := by rw [h1, h2]
  exact h
```

`obtain ⟨x, hx⟩ := h`: take apart a hypothesis that says something exists, or
a conjunction.

```lean
example (h : ∃ n : Nat, n > 3) : ∃ m : Nat, m > 2 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by omega⟩
```

`refine ⟨a, ?_⟩`: like `exact`, with holes. Each `?_` becomes a new goal, and
each `_` is worked out by Lean.

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨hp, ?_⟩
  exact hq
```

`intro x`: to prove "for all `x`" or "if `p` then", assume `x` or `p`.

```lean
example (p q : Prop) (hq : q) : p → q := by
  intro _
  exact hq
```

`apply lemma`: reduce the goal to the hypotheses of the lemma.

```lean
example (a b : Nat) (h : a ≤ b) : a < b + 1 := by
  apply Nat.lt_succ_of_le
  exact h
```

# Asking Lean

* `exact?` searches the library for a lemma that closes the goal.
* `simp?` shows which lemmas `simp` used, so you can write `simp only`.
* `rw?` searches for a rewrite that applies.
* `#check name` shows the statement of a lemma.
* `#print axioms name` shows what a theorem ultimately rests on.
* `sorry` closes any goal, with a warning. Use it to postpone part of a proof.
