# Answers to `Review.lean`

Read after you have decided for yourself.

1. **Do not accept.** The statement was changed. It was asked for `n ≤ t`
   and it came back for `n < t`. The cycle `t = n`, the first on which a real
   input comes out, is no longer covered. Compare the returned statement with
   the one asked for, symbol by symbol. Better: ask for a proof of `Asked`
   itself, as sections 3 to 5 do, so that Lean does the comparing.

2. **Do not accept.** A hypothesis was added that nothing satisfies:
   `x (k + 1) < x k` for every `k` asks for natural numbers that decrease for
   ever. The theorem is true and says nothing. The sign is that the proof
   never uses `hx`. The test is to try to give one `x` that meets the
   hypothesis.

3. **Do not accept.** `returned` proves exactly what was asked, but it rests
   on `state_is_sum`, whose proof is `sorry`. The build prints a warning, and
   `#print axioms Specs.Review.Three.returned` lists `sorryAx`.

4. **Do not accept.** The theorem is about a different accumulator. The file
   defines its own `accumulator` above the statement, and that one shows the
   starting value in the cycle of the `clear` itself, which the doc says
   it must not. `Asked` reads as if it were about `Tau.accumulator`; put the
   cursor on the name to see which one it is. A statement that names nothing
   but definitions under `Tau/` cannot be bent this way.

5. **Accept.** It proves `Asked` as written, from a theorem of the library,
   with no added hypothesis. `#print axioms` reports no axioms at all.
