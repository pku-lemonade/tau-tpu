//===- TauOps.td - the tau dialect ---------------------------------------===//
//
// The tau dialect describes a kernel: words are loaded from buffers, combined
// by lane-wise operations, and stored back. It says nothing about slices,
// streams or cycles. Tau/IR/Kernel.lean is the Lean model of this dialect.
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

def Tau_LoadOp : Tau_Op<"load"> {
  let summary = "Load one word from a buffer";
  let arguments = (ins Tau_BufType:$buf, I64Attr:$base, I64Attr:$stride);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat =
      "$buf `[` $base `,` $stride `]` attr-dict `:` type($buf)";
}

def Tau_StoreOp : Tau_Op<"store"> {
  let summary = "Store one word to a buffer";
  let arguments = (ins Tau_WordType:$value, Tau_BufType:$buf, I64Attr:$base,
                       I64Attr:$stride);
  let assemblyFormat =
      "$value `,` $buf `[` $base `,` $stride `]` attr-dict `:` type($buf)";
}

class Tau_UnOp<string mnemonic, string desc> : Tau_Op<mnemonic, [Pure]> {
  let summary = desc;
  let arguments = (ins Tau_WordType:$a);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "$a attr-dict";
}

class Tau_UnKOp<string mnemonic, string desc> : Tau_Op<mnemonic, [Pure]> {
  let summary = desc;
  let arguments = (ins Tau_WordType:$a, I64Attr:$k);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "$a `,` $k attr-dict";
}

class Tau_BinOp<string mnemonic, string desc> : Tau_Op<mnemonic, [Pure]> {
  let summary = desc;
  let arguments = (ins Tau_WordType:$a, Tau_WordType:$b);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "$a `,` $b attr-dict";
}

def Tau_ReluOp : Tau_UnOp<"relu", "Replace negative lanes by zero">;
def Tau_RequantOp
    : Tau_UnKOp<"requant", "Divide by 2^k, then clamp to -128..127">;
def Tau_ShiftOp : Tau_UnKOp<"shift", "Move every lane up by k places">;
def Tau_RotateOp : Tau_UnKOp<"rotate", "Rotate the lanes by k places">;

def Tau_AddOp : Tau_BinOp<"add", "Lane-wise wrapping addition">;
def Tau_SubOp : Tau_BinOp<"sub", "Lane-wise wrapping subtraction">;
def Tau_MulOp : Tau_BinOp<"mul", "Lane-wise wrapping multiplication">;
def Tau_MaxOp : Tau_BinOp<"max", "Lane-wise signed maximum">;
def Tau_MinOp : Tau_BinOp<"min", "Lane-wise signed minimum">;

def Tau_MatVecOp : Tau_Op<"matvec"> {
  let summary = "Multiply a matrix by a word";
  let description = [{
    The columns of the matrix are the `n` words of `buf` starting at the given
    position. The result is the sum over `j` of lane `j` of `x` times column
    `j`.
  }];
  let arguments = (ins Tau_WordType:$x, Tau_BufType:$buf, I64Attr:$base,
                       I64Attr:$stride, I64Attr:$n);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat =
      "$x `,` $buf `[` $base `,` $stride `]` `,` $n attr-dict `:` type($buf)";
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

//===----------------------------------------------------------------------===//
// Instructions
//===----------------------------------------------------------------------===//
//
// After `tau-place` a function no longer holds kernel operations. It holds
// instructions: one operation per machine instruction, in the order the
// kernel needs them to take effect. Tau/Check/Placed.lean is the Lean model.
//
// A `!tau.word` value is now a word travelling on a stream from the slice
// that produces it to the one slice that uses it. A `!tau.acc` value links
// the instructions of one matrix-vector product.
//
// Every instruction has a `slice`. The later passes add:
//
//   time            the cycle of issue                       (tau-schedule)
//   east, stream    the stream that carries the result       (tau-route)

class Tau_Instr<string mnemonic> : Tau_Op<"i." # mnemonic>;

def Tau_IReadOp : Tau_Instr<"read"> {
  let summary = "Memory slice: put the word at `addr` on a stream";
  let arguments = (ins I64Attr:$slice, I64Attr:$addr,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "attr-dict";
}

def Tau_IWriteOp : Tau_Instr<"write"> {
  let summary = "Memory slice: store a word at `addr`";
  let arguments = (ins Tau_WordType:$value, I64Attr:$slice, I64Attr:$addr,
                       OptionalAttr<I64Attr>:$time);
  let assemblyFormat = "$value attr-dict";
}

def Tau_IUnOp : Tau_Instr<"un"> {
  let summary = "Vector or rearrangement slice: apply `fn` to one word";
  let arguments = (ins Tau_WordType:$a, StrAttr:$fn,
                       OptionalAttr<I64Attr>:$k, I64Attr:$slice,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "$a attr-dict";
}

def Tau_IBinOp : Tau_Instr<"bin"> {
  let summary = "Vector slice: apply `fn` to two words";
  let arguments = (ins Tau_WordType:$a, Tau_WordType:$b, StrAttr:$fn,
                       I64Attr:$slice, OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "$a `,` $b attr-dict";
}

def Tau_ILoadOp : Tau_Instr<"load"> {
  let summary = "Matrix slice: keep a word as the vector operand";
  let arguments = (ins Tau_WordType:$x, I64Attr:$slice,
                       OptionalAttr<I64Attr>:$time);
  let results = (outs Tau_AccType:$state);
  let assemblyFormat = "$x attr-dict";
}

def Tau_IMacOp : Tau_Instr<"mac"> {
  let summary =
      "Matrix slice: add lane `j` of the vector operand times a word";
  let arguments = (ins Tau_AccType:$state, Tau_WordType:$w, I64Attr:$j,
                       I64Attr:$slice, OptionalAttr<I64Attr>:$time);
  let results = (outs Tau_AccType:$next);
  let assemblyFormat = "$state `,` $w attr-dict";
}

def Tau_IEmitOp : Tau_Instr<"emit"> {
  let summary = "Matrix slice: put the accumulator on a stream and clear it";
  let arguments = (ins Tau_AccType:$state, I64Attr:$slice,
                       OptionalAttr<I64Attr>:$time,
                       OptionalAttr<BoolAttr>:$east,
                       OptionalAttr<I64Attr>:$stream);
  let results = (outs Tau_WordType:$result);
  let assemblyFormat = "$state attr-dict";
}

#endif // TAU_OPS_TD
