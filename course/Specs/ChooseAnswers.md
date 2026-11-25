# Notes on "Choose"

Read after you have written your own answers. These are one person's
judgement. A different answer with a good reason is a good answer.

The three questions that decide it:

1. **How many right outputs are there?** If one, a copy can be compared with
   the real pass line by line. If many, a copy would have to make the same
   arbitrary choices as the C++, and a check or a rule is the only way.
2. **How often will the pass change?** A copy has to be changed every time
   the C++ is. A check does not care how the output was found.
3. **Does anybody need to be told what a right output is?** A check answers
   yes or no. A rule is a definition somebody can read and aim for.

## The five passes of tau-tpu

| Pass | Choice | Why |
|---|---|---|
| `tau-simplify` | a check, as now; a copy would also do | Three fixed rewrites and one right output, so a copy is possible, and you wrote one. But the list of rewrites is the part most likely to grow, and each new one would need the copy and its proof changed. The check needs only the new law. |
| `tau-unroll` | a copy, as now, and a check | One right output, twenty lines, never changes. The copy found a bug in the C++ that no example had reached. |
| `tau-place` | a check | Hundreds of lines of heuristics with many right outputs. Nobody would keep a copy in step. |
| `tau-schedule` | a check, and a rule | The check gives the guarantee. A rule (every operand arrives on time, one instruction per slice per cycle) is what a person writing a second scheduler needs, and what a rejection message should quote. |
| `tau-route` | a check, and a rule | The same. The rule is short: no two words in one stream slot. |

## Five passes tau-tpu does not have

| Pass | Choice | Why |
|---|---|---|
| Constant folding | a check | It is `tau-simplify` with more laws. Evaluate both sides on names and compare, with the simplifier knowing the folds. |
| Removing stores that are never read | a check | The output computes the same final buffers only if "never read" was decided rightly, which a check on final buffers tests directly. Note what the statement has to say when the removed store would have failed. |
| A register allocator | a check, or a rule | Many right outputs. The classic answer is a check: this is how CompCert validates its allocator. The rule would be "no two values that are alive at once share a register". |
| A scheduler that calls an integer-program solver | a check | Nobody can copy a solver. The solver's answer is checked, and the solver is not trusted at all. |
| An encoder from instructions to bits | a rule, about two passes | The property is that decoding gives back what was encoded. It mentions the encoder and the decoder together, and neither has a meaning on its own. A copy of one of them proves nothing. |
