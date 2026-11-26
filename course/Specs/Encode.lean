import Specs.Tables

set_option linter.unusedVariables false

/-!
# Specify: a program as numbers

Source: `Tau/Docs/Machine.md`, section 3.10.

The types are `Track`, `Instr` and `Timed` in `Tau/Isa/Instr.lean`.

The steps are the ones in `course/Specs/Kernel.lean`. Here there is no second
table: the doc's tables decide everything these four functions do. What
the doc leaves open is in the questions at the end.
-/

namespace Specs.Encode

open Tau Specs

/-- A stream as a number. -/
def encodeTrack (tr : Track) : Nat := todo

/-- The stream a number stands for. -/
def decodeTrack (n : Nat) : Track := todo

/-- A signed integer as a number. -/
def encodeSigned (z : Int) : Nat := todo

/-- The signed integer a number stands for. -/
def decodeSigned (n : Nat) : Int := todo

#eval report "streams and integers" (Tables.numbers encodeTrack encodeSigned)
#eval report "and back" (Tables.numbersBack decodeTrack decodeSigned)

/-- An entry as numbers. Write the cases for `read` and `write`, with your
`encodeTrack`. The other instructions are given by `Instr.encode`, the
finished encoding, so that the last four rows of the table can agree. -/
def encodeEntry (e : Timed) : List Nat :=
  match e.instr with
  | .read addr dst => todo
  | .write src addr => todo
  | i => e.time :: e.repeats :: e.gap :: e.stride :: i.encode

#eval report "entries" (Tables.entries encodeEntry)

/-! ## State -/

/-- The property of your first two functions that the compiler relies on:
what it writes can be read back. -/
def TrackSurvives : Prop := todo

/-- The other direction: every number is the number of a stream. -/
def EveryNumberIsATrack : Prop := todo

/-! ## Judge

Answer in `course/Work/Questions.md`.

1. Both statements are true of streams. Which of the two is false for
   instructions, and what is a number that shows it?
2. The compiler needs only the encoder. Why does the specification need the
   decoder?
3. The numbers have no fixed width. A real format packs each into a field of
   so many bits. Which of your two statements needs a hypothesis then, and
   what is it?
4. A slice's list starts with its number of entries. What could `decode` not
   do without it, given that an entry has no fixed length?

## Compare

The definitions are in `Tau/Isa/Encode.lean`. The statements are
`Track.decode_encode` and, for the whole image, `Image.decode_encode` in
`Tau/Proofs/Isa/Encode.lean`; the second is `DecodeInvertsEncode` in
`Tau/Claims.lean`. Nothing in `Tau/` states the other direction.

An encoder is one function, and "it is right" is a statement about two: the
encoder and the decoder that says what the numbers mean. The decoder is the
specification. This is the answer to the last question of the exercise
"Choose" in the chapter on the checker.
-/

end Specs.Encode
