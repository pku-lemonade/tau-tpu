import Tau.Isa.Encode

/-!
# Reading an image back gives the program

The main result is `Image.decode_encode`: the image of a program, decoded, is
the program again, with its entries grouped by slice.

The proof goes one layer at a time, and each layer has the same statement:
decoding what was encoded, with any numbers `r` after it, gives the thing
back and leaves `r`. Streams and integers first, then operations,
instructions, entries, a slice's list, and the whole image.
-/

namespace Tau

theorem Stream.decode_encode (tr : Stream) : Stream.decode tr.encode = tr := by
  obtain ⟨dir, id⟩ := tr
  cases dir <;> simp [Stream.encode, Stream.decode] <;> omega

theorem decodeInt_encodeInt (z : Int) : decodeInt (encodeInt z) = z := by
  cases z <;> simp [encodeInt, decodeInt] <;> omega

theorem decodeInt_comp_encodeInt : decodeInt ∘ encodeInt = id :=
  funext decodeInt_encodeInt

theorem DType.decode_encode (ty : DType) : DType.decode ty.encode = some ty := by
  cases ty <;> rfl

theorem UnOp.decode_encode (op : UnOp) (r : List Nat) :
    UnOp.decode (op.encode ++ r) = some (op, r) := by
  cases op <;> simp [UnOp.encode, UnOp.decode, decodeInt_encodeInt, DType.decode_encode]

theorem BinOp.decode_encode (op : BinOp) : BinOp.decode op.encode = some op := by
  cases op <;> rfl

theorem Instr.decode_encode (i : Instr) (r : List Nat) :
    Instr.decode (i.encode ++ r) = some (i, r) := by
  cases i <;>
    simp [Instr.encode, Instr.decode, Stream.decode_encode, UnOp.decode_encode,
      BinOp.decode_encode, DType.decode_encode, decodeInt_comp_encodeInt]

/-- An entry read back is the entry, at the slice whose list it was in. -/
theorem TimedEntry.decode_encode (p : Nat) (e : TimedEntry) (r : List Nat) :
    TimedEntry.decode p (e.encode ++ r) = some ({ e with slice := p }, r) := by
  simp [TimedEntry.encode, TimedEntry.decode, Instr.decode_encode]

theorem decodeEntries_encode (p : Nat) (es : List TimedEntry) (r : List Nat) :
    decodeEntries p es.length (es.flatMap TimedEntry.encode ++ r) =
      some (es.map fun e => { e with slice := p }, r) := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeEntries,
      TimedEntry.decode_encode, ih, List.map_cons]

theorem decodeSlice_encodeSlice (p : Nat) (es : List TimedEntry) :
    decodeSlice p (encodeSlice es) = some (es.map fun e => { e with slice := p }) := by
  have h := decodeEntries_encode p es []
  simp only [List.append_nil] at h
  simp only [encodeSlice, decodeSlice, h]

/-- The entries of slice `p` already have `p` as their slice. -/
theorem entriesOf_slice (prog : Program) (p : Nat) :
    ((prog.entriesOf p).map fun e => { e with slice := p }) = prog.entriesOf p := by
  unfold Program.entriesOf
  induction prog with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.filter_cons]
    split
    · rename_i h
      have hp : e.slice = p := by simpa using h
      simp only [List.map_cons, ih]
      rw [← hp]
    · exact ih

theorem decodeSlices_encode (prog : Program) (p n : Nat) :
    decodeSlices p ((List.range' p n).map fun q => encodeSlice (prog.entriesOf q)) =
      some ((List.range' p n).flatMap fun q => prog.entriesOf q) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [List.range'_succ, List.map_cons, decodeSlices, decodeSlice_encodeSlice,
      entriesOf_slice, ih, List.flatMap_cons]

/-- **Reading an image back gives the program.** The image of a program for a
machine with `slices` slices, decoded, is the program's entries for slice 0,
then for slice 1, and so on. -/
theorem Image.decode_encode (prog : Program) (slices : Nat) :
    Image.decode (prog.encode slices) =
      some ((List.range slices).flatMap fun p => prog.entriesOf p) := by
  unfold Image.decode Program.encode
  rw [List.range_eq_range']
  exact decodeSlices_encode prog 0 slices

end Tau
