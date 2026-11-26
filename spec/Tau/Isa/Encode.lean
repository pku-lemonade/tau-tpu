import Tau.Isa.Instr

/-!
# The image: a program as numbers

The last thing the compiler writes is the *image*: for each slice, the list
of numbers that is loaded into the slice's repeater. This file says how an
entry of a program becomes numbers (`encode`) and how the numbers are read
back (`decode`).

`decode` is what gives an image its meaning: the machine loaded with an image
does what `execute` (`Tau.Machine.Arch`) does with the decoded
program. `encode` is the Lean copy of the last step of the compiler. That
reading back what was written gives the program again is proved in
`Tau.Proofs.Isa.Encode`.

An image has one list per slice, so an entry does not store its slice. The
list of a slice starts with the number of entries. Each entry is

    time, repeats, gap, stride, opcode, operands...

A stream is one number: twice its number, plus one if it goes west. A signed
integer is one number: `2 * n` for `n ≥ 0`, and `2 * n - 1` for `-n`. A list is
its length and then its items.

The numbers here have no fixed width. A real instruction format packs them
into bit fields, which adds a bound on every field and nothing else.

Terms to look up: *instruction encoding*, *assembler*, *zigzag encoding*.

Docs: Machine 3.10 (`docs/`).
-/

namespace Tau

/-- A stream as a number. -/
def Track.encode (tr : Track) : Nat :=
  match tr.dir with
  | .east => 2 * tr.id
  | .west => 2 * tr.id + 1

/-- The stream a number stands for. -/
def Track.decode (n : Nat) : Track :=
  ⟨if n % 2 = 0 then .east else .west, n / 2⟩

/-- A signed integer as a number. -/
def encodeInt : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

/-- The signed integer a number stands for. -/
def decodeInt (n : Nat) : Int :=
  if n % 2 = 0 then .ofNat (n / 2) else .negSucc (n / 2)

/-- A one-word operation as numbers: its code, then what it takes. -/
def UnOp.encode : UnOp → List Nat
  | .relu => [0]
  | .requant k => [1, k]
  | .neg => [2]
  | .abs => [3]
  | .shl k => [4, k]
  | .addi c => [5, encodeInt c]
  | .muli c => [6, encodeInt c]
  | .shift k => [7, k]
  | .rotate k => [8, k]
  | .reverse => [9]
  | .broadcast j => [10, j]
  | .permute table => 11 :: table.length :: table

/-- Read a one-word operation from the front of a list of numbers. Returns
the operation and the numbers after it. -/
def UnOp.decode : List Nat → Option (UnOp × List Nat)
  | 0 :: r => some (.relu, r)
  | 1 :: k :: r => some (.requant k, r)
  | 2 :: r => some (.neg, r)
  | 3 :: r => some (.abs, r)
  | 4 :: k :: r => some (.shl k, r)
  | 5 :: c :: r => some (.addi (decodeInt c), r)
  | 6 :: c :: r => some (.muli (decodeInt c), r)
  | 7 :: k :: r => some (.shift k, r)
  | 8 :: k :: r => some (.rotate k, r)
  | 9 :: r => some (.reverse, r)
  | 10 :: j :: r => some (.broadcast j, r)
  | 11 :: n :: r => if n ≤ r.length then some (.permute (r.take n), r.drop n) else none
  | _ => none

/-- A two-word operation as a number. -/
def BinOp.encode : BinOp → Nat
  | .add => 0
  | .sub => 1
  | .mul => 2
  | .max => 3
  | .min => 4
  | .and => 5
  | .or => 6
  | .xor => 7
  | .lt => 8

/-- The two-word operation a number stands for. -/
def BinOp.decode : Nat → Option BinOp
  | 0 => some .add
  | 1 => some .sub
  | 2 => some .mul
  | 3 => some .max
  | 4 => some .min
  | 5 => some .and
  | 6 => some .or
  | 7 => some .xor
  | 8 => some .lt
  | _ => none

/-- An instruction as numbers: its opcode, then its operands. -/
def Instr.encode : Instr → List Nat
  | .read addr dst => [0, addr, dst.encode]
  | .write src addr => [1, src.encode, addr]
  | .un op src dst => 2 :: src.encode :: dst.encode :: op.encode
  | .bin op a b dst => [3, op.encode, a.encode, b.encode, dst.encode]
  | .load src => [4, src.encode]
  | .mac j src => [5, j, src.encode]
  | .emit dst => [6, dst.encode]
  | .const xs dst => 7 :: dst.encode :: xs.length :: xs.map encodeInt
  | .sel m a b dst => [8, m.encode, a.encode, b.encode, dst.encode]
  | .seed src => [9, src.encode]
  | .install j src => [10, j, src.encode]
  | .macw j => [11, j]

/-- Read an instruction from the front of a list of numbers. -/
def Instr.decode : List Nat → Option (Instr × List Nat)
  | 0 :: addr :: dst :: r => some (.read addr (.decode dst), r)
  | 1 :: src :: addr :: r => some (.write (.decode src) addr, r)
  | 2 :: src :: dst :: r =>
    match UnOp.decode r with
    | some (op, r') => some (.un op (.decode src) (.decode dst), r')
    | none => none
  | 3 :: op :: a :: b :: dst :: r =>
    match BinOp.decode op with
    | some op => some (.bin op (.decode a) (.decode b) (.decode dst), r)
    | none => none
  | 4 :: src :: r => some (.load (.decode src), r)
  | 5 :: j :: src :: r => some (.mac j (.decode src), r)
  | 6 :: dst :: r => some (.emit (.decode dst), r)
  | 7 :: dst :: n :: r =>
    if n ≤ r.length then some (.const ((r.take n).map decodeInt) (.decode dst), r.drop n)
    else none
  | 8 :: m :: a :: b :: dst :: r =>
    some (.sel (.decode m) (.decode a) (.decode b) (.decode dst), r)
  | 9 :: src :: r => some (.seed (.decode src), r)
  | 10 :: j :: src :: r => some (.install j (.decode src), r)
  | 11 :: j :: r => some (.macw j, r)
  | _ => none

/-- An entry as numbers. Its slice is not stored. -/
def Timed.encode (e : Timed) : List Nat :=
  e.time :: e.repeats :: e.gap :: e.stride :: e.instr.encode

/-- Read an entry of slice `p` from the front of a list of numbers. -/
def Timed.decode (p : Nat) : List Nat → Option (Timed × List Nat)
  | time :: repeats :: gap :: stride :: r =>
    match Instr.decode r with
    | some (instr, r') => some (⟨p, time, instr, repeats, gap, stride⟩, r')
    | none => none
  | _ => none

/-- Read `n` entries of slice `p` from the front of a list of numbers. -/
def decodeEntries (p : Nat) : Nat → List Nat → Option (List Timed × List Nat)
  | 0, r => some ([], r)
  | n + 1, r =>
    match Timed.decode p r with
    | some (e, r') =>
      match decodeEntries p n r' with
      | some (es, r'') => some (e :: es, r'')
      | none => none
    | none => none

/-- The entries of one slice as numbers: how many, then each. -/
def encodeSlice (es : List Timed) : List Nat :=
  es.length :: es.flatMap Timed.encode

/-- Read the entries of slice `p` from its list of numbers. Every number must
be used. -/
def decodeSlice (p : Nat) : List Nat → Option (List Timed)
  | n :: r =>
    match decodeEntries p n r with
    | some (es, []) => some es
    | _ => none
  | [] => none

/-- A program as numbers. -/
abbrev Image := List (List Nat)

/-- The image of a program for a machine with `slices` slices. -/
def Program.encode (prog : Program) (slices : Nat) : Image :=
  (List.range slices).map fun p => encodeSlice (prog.entriesOf p)

/-- Read the lists of an image, the first of which belongs to slice `p`. -/
def decodeSlices : Nat → Image → Option Program
  | _, [] => some []
  | p, ws :: rest =>
    match decodeSlice p ws, decodeSlices (p + 1) rest with
    | some es, some more => some (es ++ more)
    | _, _ => none

/-- The program an image stands for. `none` if the image is not well
formed. -/
def Image.decode (image : Image) : Option Program := decodeSlices 0 image

end Tau
