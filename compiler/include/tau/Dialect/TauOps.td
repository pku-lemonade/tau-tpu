//===- TauOps.td - the tau dialect ---------------------------------------===//
//
// The tau dialect describes a kernel: words are loaded from buffers, combined
// by lane-wise operations, and stored back. It says nothing about slices or
// streams. spec/Tau/IR/Kernel.lean is the Lean model of this dialect, and
// spec/Tau/IR/Source.lean of a module in which kernels call each other.
//
// The dialect has three groups of operations, for the three shapes a program
// takes in the compiler:
//
//   tau.load, tau.add, ...   kernel operations         (before tau-place)
//   tau.i.read, tau.i.un ... instructions, joined by   (tau-place to
//                            the words they pass on     tau-route)
//   tau.slice, tau.entry     one list of entries per   (after tau-slice)
//                            slice, naming streams
//
//===----------------------------------------------------------------------===//

#ifndef TAU_OPS_TD
#define TAU_OPS_TD

include "mlir/IR/OpBase.td"
include "mlir/IR/AttrTypeBase.td"
include "mlir/Interfaces/SideEffectInterfaces.td"

def Tau_Dialect : Dialect {
  let name = "tau";
  let cppNamespace = "::tau";
  let summary = "Kernels for the tau-tpu tensor processor";
  let useDefaultTypePrinterParser = 1;
}

//===----------------------------------------------------------------------===//
// Types
//===----------------------------------------------------------------------===//

class Tau_Type<string name, string typeMnemonic>
    : TypeDef<Tau_Dialect, name> {
  let mnemonic = typeMnemonic;
}

def Tau_WordType : Tau_Type<"Word", "word"> {
  let summary = "One word: a fixed number of lanes, each a byte";
}

def Tau_IntType : Tau_Type<"Int", "int"> {
  let summary = "A value: for every lane a signed integer of `bits` bits";
  let description = [{
    `bits` is 8, 16 or 32. On the machine a value is `bits / 8` words
    (Machine 1).
  }];
  let parameters = (ins "unsigned":$bits);
  let assemblyFormat = "`<` $bits `>`";
  let genVerifyDecl = 1;
}

// A value of 8 bits and a value of 32 bits, where an operation takes or gives
// no other.
def Tau_Int8 : Type<And<[Tau_IntType.predicate,
                         CPred<"::llvm::cast<::tau::IntType>($_self).getBits() == 8">]>,
                    "a value of 8 bits">,
               BuildableType<"::tau::IntType::get($_builder.getContext(), 8)">;
def Tau_Int32 : Type<And<[Tau_IntType.predicate,
                          CPred<"::llvm::cast<::tau::IntType>($_self).getBits() == 32">]>,
                     "a value of 32 bits">,
                BuildableType<"::tau::IntType::get($_builder.getContext(), 32)">;

def Tau_PlaneType : Tau_Type<"Plane", "plane"> {
  let summary = "The installed words of a matrix slice between two installs of one matrix";
}

def Tau_BufType : Tau_Type<"Buf", "buf"> {
  let summary = "A buffer of `size` values of `bits` bits each";
  let parameters = (ins "unsigned":$size, "unsigned":$bits);
  let assemblyFormat = "`<` $size `x` $bits `>`";
  let genVerifyDecl = 1;
}

// The type of the values a buffer holds.
class Tau_ValueOf<string buf, string value>
    : TypesMatchWith<"the value has the type the buffer holds", buf, value,
                     "::tau::IntType::get($_self.getContext(), "
                     "::llvm::cast<::tau::BufType>($_self).getBits())">;

//===----------------------------------------------------------------------===//
// Operations
//===----------------------------------------------------------------------===//

class Tau_Op<string mnemonic, list<Trait> traits = []>
    : Op<Tau_Dialect, mnemonic, traits>;

// A position in a buffer is written `[base, stride]` and means
// `base + stride * i`, where `i` is the index of the enclosing `tau.for`, or 0
// outside a loop.
//
// Any operation may be pinned: `at t` says that its value is issued on cycle
// `t`, counted from the start of its kernel. For an operation with a result
// the value is the result; for a store it is the value stored. Inside a loop,
// `at t every d` means cycle `t + d * i`. spec/Tau/Isa/Event.lean says what a pin
// claims.

// An operation that only computes a value may be removed when nothing uses
// the value, unless it is pinned: a pinned value has to be issued on its
// cycle, used or not. So such an operation has no effect when it has no pin,
// and one when it has.
class Tau_ValueOp<string mnemonic, list<Trait> traits = []>
    : Tau_Op<mnemonic,
             !listconcat([DeclareOpInterfaceMethods<MemoryEffectsOpInterface>],
                         traits)> {
  let extraClassDefinition = [{
    void $cppClass::getEffects(
        ::llvm::SmallVectorImpl<::mlir::MemoryEffects::EffectInstance>
            &effects) {
      if (getAt())
        effects.emplace_back(::mlir::MemoryEffects::Write::get());
    }
  }];
}

def Tau_LoadOp : Tau_Op<"load", [Tau_ValueOf<"buf", "result">]> {
  let summary = "Load one value from a buffer";
  let arguments = (ins Tau_BufType:$buf, I64Attr:$base, I64Attr:$stride,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_IntType:$result);
  let assemblyFormat = [{
    $buf `[` $base `,` $stride `]` (`at` $at^)? (`every` $every^)? attr-dict `:` type($buf)
  }];
}

def Tau_StoreOp : Tau_Op<"store", [Tau_ValueOf<"buf", "value">]> {
  let summary = "Store one value to a buffer";
  let arguments = (ins Tau_IntType:$value, Tau_BufType:$buf, I64Attr:$base, I64Attr:$stride,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let assemblyFormat = [{
    $value `,` $buf `[` $base `,` $stride `]` (`at` $at^)? (`every` $every^)? attr-dict `:` type($buf)
  }];
}

// A one-value operation that gives a value of the type it takes.
class Tau_UnOp<string mnemonic, string desc>
    : Tau_ValueOp<mnemonic, [AllTypesMatch<["a", "result"]>]> {
  let summary = desc;
  let arguments = (ins Tau_IntType:$a,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_IntType:$result);
  let assemblyFormat = [{
    $a (`at` $at^)? (`every` $every^)? attr-dict `:` type($a)
  }];
}

class Tau_UnKOp<string mnemonic, string desc>
    : Tau_ValueOp<mnemonic, [AllTypesMatch<["a", "result"]>]> {
  let summary = desc;
  let arguments = (ins Tau_IntType:$a, I64Attr:$k,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_IntType:$result);
  let assemblyFormat = [{
    $a `,` $k (`at` $at^)? (`every` $every^)? attr-dict `:` type($a)
  }];
}

class Tau_BinOp<string mnemonic, string desc>
    : Tau_ValueOp<mnemonic, [AllTypesMatch<["a", "b", "result"]>]> {
  let summary = desc;
  let arguments = (ins Tau_IntType:$a, Tau_IntType:$b,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_IntType:$result);
  let assemblyFormat = [{
    $a `,` $b (`at` $at^)? (`every` $every^)? attr-dict `:` type($a)
  }];
}

// Vector slice.
def Tau_ReluOp : Tau_UnOp<"relu", "Replace negative elements by zero">;
def Tau_NegOp : Tau_UnOp<"neg", "Negate every element">;
def Tau_AbsOp : Tau_UnOp<"abs", "The absolute value of every element">;
def Tau_ShlOp : Tau_UnKOp<"shl", "Shift the bits of every element left by k">;
def Tau_AddiOp : Tau_UnKOp<"addi", "Add the constant k to every element">;
def Tau_MuliOp : Tau_UnKOp<"muli", "Multiply every element by the constant k">;

def Tau_RequantOp : Tau_ValueOp<"requant"> {
  let summary = "Divide by 2^k, then clamp to -128..127: a value of 8 bits";
  let arguments = (ins Tau_IntType:$a, I64Attr:$k,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_Int8:$result);
  let assemblyFormat = [{
    $a `,` $k (`at` $at^)? (`every` $every^)? attr-dict `:` type($a)
  }];
}

def Tau_WidenOp : Tau_ValueOp<"widen"> {
  let summary = "The same elements as a value of more bits";
  let arguments = (ins Tau_IntType:$a,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_IntType:$result);
  let assemblyFormat = [{
    $a (`at` $at^)? (`every` $every^)? attr-dict `:` type($a) `to` type($result)
  }];
  let hasVerifier = 1;
}

// Rearrangement slice.
def Tau_ShiftOp : Tau_UnKOp<"shift", "Move every element up by k places">;
def Tau_RotateOp : Tau_UnKOp<"rotate", "Rotate the elements by k places">;
def Tau_ReverseOp : Tau_UnOp<"reverse", "Put the elements in opposite order">;
def Tau_BroadcastOp : Tau_UnKOp<"broadcast", "Copy element k to every element">;

def Tau_PermuteOp
    : Tau_ValueOp<"permute", [AllTypesMatch<["a", "result"]>]> {
  let summary = "Element i takes the value of element table[i]";
  let arguments = (ins Tau_IntType:$a, DenseI64ArrayAttr:$table,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_IntType:$result);
  let assemblyFormat = [{
    $a `,` $table (`at` $at^)? (`every` $every^)? attr-dict `:` type($a)
  }];
}

def Tau_AddOp : Tau_BinOp<"add", "Wrapping addition, element by element">;
def Tau_SubOp : Tau_BinOp<"sub", "Wrapping subtraction, element by element">;
def Tau_MulOp : Tau_BinOp<"mul", "Wrapping multiplication, element by element">;
def Tau_MaxOp : Tau_BinOp<"max", "Signed maximum, element by element">;
def Tau_MinOp : Tau_BinOp<"min", "Signed minimum, element by element">;
def Tau_AndOp : Tau_BinOp<"and", "Bit-wise and">;
def Tau_OrOp : Tau_BinOp<"or", "Bit-wise or">;
def Tau_XorOp : Tau_BinOp<"xor", "Bit-wise exclusive or">;
def Tau_LtOp
    : Tau_BinOp<"lt", "Element by element: 1 where the first is less, else 0">;

def Tau_ConstOp : Tau_ValueOp<"const"> {
  let summary = "The constant with the given elements";
  let arguments = (ins DenseI64ArrayAttr:$values,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_IntType:$result);
  let assemblyFormat = [{
    $values (`at` $at^)? (`every` $every^)? attr-dict `:` type($result)
  }];
}

def Tau_SelectOp
    : Tau_ValueOp<"select", [AllTypesMatch<["m", "a", "b", "result"]>]> {
  let summary = "Element by element: a where m is not zero, b elsewhere";
  let arguments = (ins Tau_IntType:$m, Tau_IntType:$a, Tau_IntType:$b,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_IntType:$result);
  let assemblyFormat = [{
    $m `,` $a `,` $b (`at` $at^)? (`every` $every^)? attr-dict `:` type($a)
  }];
}

def Tau_MatVecOp : Tau_ValueOp<"matvec"> {
  let summary = "Multiply a matrix by a value";
  let description = [{
    The matrix is the `n` values of 8 bits of `buf` starting at the given
    position. Value `i` holds the weights of element `i` of the result:
    element `i` is the sum over `j` of element `j` of value `i` times element
    `j` of `x`. The elements from `n` on are zero. `x` has 8 bits and the
    result 32.
  }];
  let arguments = (ins Tau_Int8:$x, Tau_BufType:$buf, I64Attr:$base, I64Attr:$stride, I64Attr:$n,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_Int32:$result);
  let assemblyFormat = [{
    $x `,` $buf `[` $base `,` $stride `]` `,` $n (`at` $at^)? (`every` $every^)? attr-dict `:` type($buf)
  }];
}

def Tau_ForOp : Tau_Op<"for", [SingleBlock, NoTerminator]> {
  let summary = "Run the body n times";
  let description = [{
    Positions inside the body may depend on the iteration through their
    stride. Loops do not nest.
  }];
  let arguments = (ins I64Attr:$n);
  let regions = (region SizedRegion<1>:$body);
  let assemblyFormat = "$n $body attr-dict";
}

def Tau_CallOp : Tau_Op<"call"> {
  let summary = "Run another kernel on some of this kernel's buffers";
  let description = [{
    The buffers of `callee` stand for the buffers given, in order. No buffer
    may be given twice. The pins of `callee` count from cycle `at` of the
    caller, or from the caller's own start if `at` is left out. `tau-inline`
    replaces the call by the body of `callee`. A call must not be inside a
    `tau.for`.
  }];
  let arguments = (ins FlatSymbolRefAttr:$callee, Variadic<Tau_BufType>:$args,
                       OptionalAttr<I64Attr>:$at);
  let assemblyFormat = [{
    $callee `(` $args `)` (`at` $at^)? attr-dict `:` `(` type($args) `)`
  }];
}

//===----------------------------------------------------------------------===//
// Instructions
//===----------------------------------------------------------------------===//
//
// After `tau-place` a function no longer holds kernel operations. It holds
// instructions: one operation per machine instruction, in the order the
// kernel needs them to take effect. spec/Tau/IR/Placed.lean is the Lean model.
//
// A `!tau.word` value is now a word travelling on a stream from the slice
// that produces it to the slices that use it. A value of the kernel is one,
// two or four of them, the low word first. A `!tau.plane` value links the
// `install`s of one matrix.
//
// Every instruction has a `slice`, and a `pin` if the kernel operation it
// issues the word of was pinned. The later passes add:
//
//   time            the cycle of issue                       (tau-schedule)
//   east, stream    the stream that carries the result       (tau-route)
//
// `tau-schedule` also adds instructions: a read of a buffer word for each
// instruction that uses it, and for a word that has to wait a write to a
// scratch word and the reads that take it out again.

class Tau_Instr<string mnemonic> : Tau_Op<"i." # mnemonic>;

def Tau_IReadOp : Tau_Instr<"read"> {
  let summary = "Memory slice: put the word at `addr` on a stream";
  let arguments = (ins I64Attr:$slice, I64Attr:$addr,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "attr-dict";
}

def Tau_IWriteOp : Tau_Instr<"write"> {
  let summary = "Memory slice: store a word at `addr`";
  let arguments = (ins Tau_WordType:$value, I64Attr:$slice, I64Attr:$addr,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time);
  let assemblyFormat = "$value attr-dict";
}

// An instruction of the vector or rearrangement slice has `bits`, the type
// of the values it takes, and takes each value as `bits / 8` words, one
// value after another. Its results are the words of the value it gives.

def Tau_IUnOp : Tau_Instr<"un"> {
  let summary = "Vector or rearrangement slice: apply `fn` to one value";
  let description = [{
    `widen` has `to`, the bits of its result. `requant` gives 8 bits.
  }];
  let arguments = (ins Variadic<Tau_WordType>:$a, StrAttr:$fn, I64Attr:$bits,
                       OptionalAttr<I64Attr>:$k,
                       OptionalAttr<I64Attr>:$to,
                       OptionalAttr<DenseI64ArrayAttr>:$table,
                       I64Attr:$slice,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Variadic<Tau_WordType>:$result);
  let assemblyFormat = "$a attr-dict `:` type($result)";
}

def Tau_IBinOp : Tau_Instr<"bin"> {
  let summary = "Vector slice: apply `fn` to two values";
  let arguments = (ins Variadic<Tau_WordType>:$operands, StrAttr:$fn,
                       I64Attr:$bits,
                       I64Attr:$slice, OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Variadic<Tau_WordType>:$result);
  let assemblyFormat = "$operands attr-dict `:` type($result)";
}

def Tau_IConstOp : Tau_Instr<"const"> {
  let summary = "Vector slice: put a constant on streams";
  let arguments = (ins DenseI64ArrayAttr:$values, I64Attr:$bits,
                       I64Attr:$slice,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Variadic<Tau_WordType>:$result);
  let assemblyFormat = "attr-dict `:` type($result)";
}

def Tau_ISelOp : Tau_Instr<"sel"> {
  let summary = "Vector slice: select, element by element";
  let description = [{ The operands are the mask, then `a`, then `b`. }];
  let arguments = (ins Variadic<Tau_WordType>:$operands, I64Attr:$bits,
                       I64Attr:$slice, OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Variadic<Tau_WordType>:$result);
  let assemblyFormat = "$operands attr-dict `:` type($result)";
}

def Tau_IInstallOp : Tau_Instr<"install"> {
  let summary = "Matrix slice: keep words as installed words `j`, `j + 1`, ...";
  let description = [{
    The operands are the words, in order. A last operand of type
    `!tau.plane` links this instruction to the previous `install` of the same
    matrix, so that the words of one matrix are installed on consecutive
    cycles.
  }];
  let arguments = (ins Variadic<AnyTypeOf<[Tau_WordType, Tau_PlaneType]>>:$operands,
                       I64Attr:$j, I64Attr:$slice,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time);
  let results = (outs Tau_PlaneType:$next);
  let assemblyFormat = "$operands attr-dict `:` type($operands)";
}

def Tau_IProductOp : Tau_Instr<"product"> {
  let summary =
      "Matrix slice: the product of the first `n` installed words with a word";
  let description = [{ The results are the four words of a value of 32 bits. }];
  let arguments = (ins Tau_WordType:$x, I64Attr:$n, I64Attr:$slice,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Variadic<Tau_WordType>:$result);
  let assemblyFormat = "$x attr-dict `:` type($result)";
}

//===----------------------------------------------------------------------===//
// Slices
//===----------------------------------------------------------------------===//
//
// After `tau-slice` a function holds one `tau.slice` for each slice of the
// machine, and in it the entries of that slice's repeater. An entry no longer
// has operands and results: it names the streams it reads and writes, as the
// machine's instructions do (`Tau.TimedEntry` in spec/Tau/Isa/Instr.lean).
// `tau-encode` then replaces each `tau.slice` by a `tau.image`.
//
// A stream is written "e3" or "w0": east or west, and its number.

def Tau_SliceOp : Tau_Op<"slice", [SingleBlock, NoTerminator]> {
  let summary = "The entries of the slice at one position";
  let arguments = (ins I64Attr:$position);
  let regions = (region SizedRegion<1>:$body);
  let assemblyFormat = "$position $body attr-dict";
}

def Tau_EntryOp : Tau_Op<"entry"> {
  let summary = "One entry of a slice's repeater";
  let description = [{
    `instr` is the instruction: read, write, un, bin, const, sel, install or
    product. `time` is the cycle of the first issue. With `repeats`, `gap`
    and `stride` the entry is issued `repeats` more times, `gap` idle cycles
    apart, with `addr` or `j` growing by `stride` each time. `tau-fold` makes
    such entries.
  }];
  let arguments = (ins StrAttr:$instr, I64Attr:$time,
                       OptionalAttr<StrAttr>:$fn,
                       OptionalAttr<I64Attr>:$k,
                       OptionalAttr<DenseI64ArrayAttr>:$table,
                       OptionalAttr<DenseI64ArrayAttr>:$values,
                       OptionalAttr<I64Attr>:$addr,
                       OptionalAttr<I64Attr>:$j,
                       OptionalAttr<I64Attr>:$g,
                       OptionalAttr<I64Attr>:$n,
                       OptionalAttr<I64Attr>:$bits,
                       OptionalAttr<I64Attr>:$to,
                       OptionalAttr<StrAttr>:$src,
                       OptionalAttr<StrAttr>:$a,
                       OptionalAttr<StrAttr>:$b,
                       OptionalAttr<StrAttr>:$m,
                       OptionalAttr<StrAttr>:$dst,
                       OptionalAttr<I64Attr>:$repeats,
                       OptionalAttr<I64Attr>:$gap,
                       OptionalAttr<I64Attr>:$stride);
  let assemblyFormat = "$instr `at` $time attr-dict";
}

//===----------------------------------------------------------------------===//
// The image
//===----------------------------------------------------------------------===//

def Tau_ImageOp : Tau_Op<"image"> {
  let summary = "The numbers the repeater of the slice at one position is loaded with";
  let description = [{
    The number of entries, then each entry as numbers: time, repeats, gap,
    stride, opcode, operands (Machine 3.10; `Program.encode` in
    spec/Tau/Isa/Encode.lean). `tau-encode` makes one for each `tau.slice`.
  }];
  let arguments = (ins I64Attr:$position, DenseI64ArrayAttr:$numbers);
  let assemblyFormat = "$position $numbers attr-dict";
}

#endif // TAU_OPS_TD
