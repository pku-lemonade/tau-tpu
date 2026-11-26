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
  let summary = "One word: a fixed number of 32-bit lanes";
}

def Tau_AccType : Tau_Type<"Acc", "acc"> {
  let summary = "The state of a matrix slice between two of its instructions";
}

def Tau_BufType : Tau_Type<"Buf", "buf"> {
  let summary = "A buffer of `size` words";
  let parameters = (ins "unsigned":$size);
  let assemblyFormat = "`<` $size `>`";
}

//===----------------------------------------------------------------------===//
// Operations
//===----------------------------------------------------------------------===//

class Tau_Op<string mnemonic, list<Trait> traits = []>
    : Op<Tau_Dialect, mnemonic, traits>;

// A position in a buffer is written `[base, stride]` and means
// `base + stride * i`, where `i` is the index of the enclosing `tau.for`, or 0
// outside a loop.
//
// Any operation may be pinned: `at t` says that its word is issued on cycle
// `t`, counted from the start of its kernel. For an operation with a result
// the word is the result; for a store it is the word stored. Inside a loop,
// `at t every d` means cycle `t + d * i`. spec/Tau/Isa/Event.lean says what a pin
// claims.

def Tau_LoadOp : Tau_Op<"load"> {
  let summary = "Load one word from a buffer";
  let arguments = (ins Tau_BufType:$buf, I64Attr:$base, I64Attr:$stride,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = [{
    $buf `[` $base `,` $stride `]` (`at` $at^)? (`every` $every^)? attr-dict `:` type($buf)
  }];
}

def Tau_StoreOp : Tau_Op<"store"> {
  let summary = "Store one word to a buffer";
  let arguments = (ins Tau_WordType:$value, Tau_BufType:$buf, I64Attr:$base, I64Attr:$stride,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let assemblyFormat = [{
    $value `,` $buf `[` $base `,` $stride `]` (`at` $at^)? (`every` $every^)? attr-dict `:` type($buf)
  }];
}

class Tau_UnOp<string mnemonic, string desc> : Tau_Op<mnemonic, [Pure]> {
  let summary = desc;
  let arguments = (ins Tau_WordType:$a,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = [{
    $a (`at` $at^)? (`every` $every^)? attr-dict
  }];
}

class Tau_UnKOp<string mnemonic, string desc> : Tau_Op<mnemonic, [Pure]> {
  let summary = desc;
  let arguments = (ins Tau_WordType:$a, I64Attr:$k,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = [{
    $a `,` $k (`at` $at^)? (`every` $every^)? attr-dict
  }];
}

class Tau_BinOp<string mnemonic, string desc> : Tau_Op<mnemonic, [Pure]> {
  let summary = desc;
  let arguments = (ins Tau_WordType:$a, Tau_WordType:$b,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = [{
    $a `,` $b (`at` $at^)? (`every` $every^)? attr-dict
  }];
}

// Vector slice.
def Tau_ReluOp : Tau_UnOp<"relu", "Replace negative lanes by zero">;
def Tau_NegOp : Tau_UnOp<"neg", "Negate every lane">;
def Tau_AbsOp : Tau_UnOp<"abs", "The absolute value of every lane">;
def Tau_RequantOp
    : Tau_UnKOp<"requant", "Divide by 2^k, then clamp to -128..127">;
def Tau_ShlOp : Tau_UnKOp<"shl", "Shift the bits of every lane left by k">;
def Tau_AddiOp : Tau_UnKOp<"addi", "Add the constant k to every lane">;
def Tau_MuliOp : Tau_UnKOp<"muli", "Multiply every lane by the constant k">;

// Rearrangement slice.
def Tau_ShiftOp : Tau_UnKOp<"shift", "Move every lane up by k places">;
def Tau_RotateOp : Tau_UnKOp<"rotate", "Rotate the lanes by k places">;
def Tau_ReverseOp : Tau_UnOp<"reverse", "Put the lanes in opposite order">;
def Tau_BroadcastOp : Tau_UnKOp<"broadcast", "Copy lane k to every lane">;

def Tau_PermuteOp : Tau_Op<"permute", [Pure]> {
  let summary = "Lane i takes the value of lane table[i]";
  let arguments = (ins Tau_WordType:$a, DenseI64ArrayAttr:$table,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = [{
    $a `,` $table (`at` $at^)? (`every` $every^)? attr-dict
  }];
}

def Tau_AddOp : Tau_BinOp<"add", "Lane-wise wrapping addition">;
def Tau_SubOp : Tau_BinOp<"sub", "Lane-wise wrapping subtraction">;
def Tau_MulOp : Tau_BinOp<"mul", "Lane-wise wrapping multiplication">;
def Tau_MaxOp : Tau_BinOp<"max", "Lane-wise signed maximum">;
def Tau_MinOp : Tau_BinOp<"min", "Lane-wise signed minimum">;
def Tau_AndOp : Tau_BinOp<"and", "Bit-wise and">;
def Tau_OrOp : Tau_BinOp<"or", "Bit-wise or">;
def Tau_XorOp : Tau_BinOp<"xor", "Bit-wise exclusive or">;
def Tau_LtOp
    : Tau_BinOp<"lt", "Lane-wise: 1 where the first is less, else 0">;

def Tau_ConstOp : Tau_Op<"const", [Pure]> {
  let summary = "The constant word with the given lanes";
  let arguments = (ins DenseI64ArrayAttr:$values,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = [{
    $values (`at` $at^)? (`every` $every^)? attr-dict
  }];
}

def Tau_SelectOp : Tau_Op<"select", [Pure]> {
  let summary = "Lane-wise: a where m is not zero, b elsewhere";
  let arguments = (ins Tau_WordType:$m, Tau_WordType:$a, Tau_WordType:$b,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = [{
    $m `,` $a `,` $b (`at` $at^)? (`every` $every^)? attr-dict
  }];
}

def Tau_MatVecOp : Tau_Op<"matvec"> {
  let summary = "Multiply a matrix by a word";
  let description = [{
    The columns of the matrix are the `n` words of `buf` starting at the given
    position. The result is the sum over `j` of lane `j` of `x` times column
    `j`.
  }];
  let arguments = (ins Tau_WordType:$x, Tau_BufType:$buf, I64Attr:$base, I64Attr:$stride, I64Attr:$n,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = [{
    $x `,` $buf `[` $base `,` $stride `]` `,` $n (`at` $at^)? (`every` $every^)? attr-dict `:` type($buf)
  }];
}

def Tau_AffineOp : Tau_Op<"affine"> {
  let summary = "Multiply a matrix by a word and add a bias word";
  let description = [{
    As `tau.matvec`, with the word `bias` added to the product.
  }];
  let arguments = (ins Tau_WordType:$x, Tau_BufType:$buf, I64Attr:$base, I64Attr:$stride, I64Attr:$n, Tau_WordType:$bias,
                       OptionalAttr<I64Attr>:$at,
                       OptionalAttr<I64Attr>:$every);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat =
      [{
    $x `,` $buf `[` $base `,` $stride `]` `,` $n `,` $bias (`at` $at^)? (`every` $every^)? attr-dict `:` type($buf)
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
// that produces it to the one slice that uses it. A `!tau.acc` value links
// the instructions of one matrix-vector product.
//
// Every instruction has a `slice`, and a `pin` if the kernel operation it
// issues the word of was pinned. The later passes add:
//
//   time            the cycle of issue                       (tau-schedule)
//   east, stream    the stream that carries the result       (tau-route)

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

def Tau_IUnOp : Tau_Instr<"un"> {
  let summary = "Vector or rearrangement slice: apply `fn` to one word";
  let arguments = (ins Tau_WordType:$a, StrAttr:$fn,
                       OptionalAttr<I64Attr>:$k,
                       OptionalAttr<DenseI64ArrayAttr>:$table,
                       I64Attr:$slice,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "$a attr-dict";
}

def Tau_IBinOp : Tau_Instr<"bin"> {
  let summary = "Vector slice: apply `fn` to two words";
  let arguments = (ins Tau_WordType:$a, Tau_WordType:$b, StrAttr:$fn,
                       I64Attr:$slice, OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "$a `,` $b attr-dict";
}

def Tau_IConstOp : Tau_Instr<"const"> {
  let summary = "Vector slice: put a constant word on a stream";
  let arguments = (ins DenseI64ArrayAttr:$values, I64Attr:$slice,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "attr-dict";
}

def Tau_ISelOp : Tau_Instr<"sel"> {
  let summary = "Vector slice: lane-wise select";
  let arguments = (ins Tau_WordType:$m, Tau_WordType:$a, Tau_WordType:$b,
                       I64Attr:$slice, OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "$m `,` $a `,` $b attr-dict";
}

def Tau_IInstallOp : Tau_Instr<"install"> {
  let summary = "Matrix slice: keep a word as stored column `j`";
  let description = [{
    The optional `state` links this instruction to the previous `install` of
    the same matrix, so that the columns are installed on consecutive cycles.
  }];
  let arguments = (ins Tau_WordType:$w, Optional<Tau_AccType>:$state,
                       I64Attr:$j, I64Attr:$slice,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time);
  let results = (outs Tau_AccType:$next);
  let assemblyFormat = "$w (`,` $state^)? attr-dict";
}

def Tau_ISeedOp : Tau_Instr<"seed"> {
  let summary = "Matrix slice: replace the accumulator by a word";
  let arguments = (ins Tau_AccType:$state, Tau_WordType:$w, I64Attr:$slice,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time);
  let results = (outs Tau_AccType:$next);
  let assemblyFormat = "$state `,` $w attr-dict";
}

def Tau_IMacwOp : Tau_Instr<"macw"> {
  let summary =
      "Matrix slice: add lane `j` of the vector operand times stored column `j`";
  let arguments = (ins Tau_AccType:$state, I64Attr:$j, I64Attr:$slice,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time);
  let results = (outs Tau_AccType:$next);
  let assemblyFormat = "$state attr-dict";
}

def Tau_ILoadOp : Tau_Instr<"load"> {
  let summary = "Matrix slice: keep a word as the vector operand";
  let arguments = (ins Tau_WordType:$x, I64Attr:$slice,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time);
  let results = (outs Tau_AccType:$state);
  let assemblyFormat = "$x attr-dict";
}

def Tau_IMacOp : Tau_Instr<"mac"> {
  let summary =
      "Matrix slice: add lane `j` of the vector operand times a word";
  let arguments = (ins Tau_AccType:$state, Tau_WordType:$w, I64Attr:$j,
                       I64Attr:$slice, OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time);
  let results = (outs Tau_AccType:$next);
  let assemblyFormat = "$state `,` $w attr-dict";
}

def Tau_IEmitOp : Tau_Instr<"emit"> {
  let summary = "Matrix slice: put the accumulator on a stream and clear it";
  let arguments = (ins Tau_AccType:$state, I64Attr:$slice,
                       OptionalAttr<I64Attr>:$pin,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "$state attr-dict";
}

//===----------------------------------------------------------------------===//
// Slices
//===----------------------------------------------------------------------===//
//
// After `tau-slice` a function holds one `tau.slice` for each slice of the
// machine, and in it the entries of that slice's repeater. An entry no longer
// has operands and results: it names the streams it reads and writes, as the
// machine's instructions do (`Tau.Timed` in spec/Tau/Isa/Instr.lean).
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
    `instr` is the instruction: read, write, un, bin, const, sel, load, seed,
    mac, install, macw or emit. `time` is the cycle of the first issue. With
    `repeats`, `gap` and `stride` the entry is issued `repeats` more times,
    `gap` idle cycles apart, with `addr` or `j` growing by `stride` each
    time. `tau-fold` makes such entries.
  }];
  let arguments = (ins StrAttr:$instr, I64Attr:$time,
                       OptionalAttr<StrAttr>:$fn,
                       OptionalAttr<I64Attr>:$k,
                       OptionalAttr<DenseI64ArrayAttr>:$table,
                       OptionalAttr<DenseI64ArrayAttr>:$values,
                       OptionalAttr<I64Attr>:$addr,
                       OptionalAttr<I64Attr>:$j,
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
