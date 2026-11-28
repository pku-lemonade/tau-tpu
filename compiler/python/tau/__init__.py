"""tau: write tau-tpu programs in Python.

A program is a Python function, marked `@tau.kernel`, that takes buffers and
calls the operations of this module on them:

    import tau
    from tau import T

    @tau.kernel
    def scale(x: tau.Buf[4], y: tau.Buf[4]):
        for i in tau.loop(4):
            v = tau.load(x, i)
            r = tau.relu(v, at=T + 6 + 4 * i)
            tau.store(y, i, r)

    kernel = scale

The function is not translated. It is *run*, once, and each operation it
calls is traced. The trace is a source program: `Source` in
spec/Tau/IR/Source.lean says what it computes and when. So Python is the language
the program is written with, and the trace is the program.

What follows from that:

  * A value is a handle with no operators. Python cannot add two values or
    test one, so what a program does cannot depend on its data. That is the
    property the machine has, and the one every check rests on.
  * A value has a type, `tau.i8`, `tau.i16` or `tau.i32`: its elements are
    signed integers of that many bits. A buffer holds values of one type,
    `tau.Buf[4]` of 8 bits and `tau.Buf[4, tau.i32]` of 32. An operation
    takes values of one type; `requant` gives 8 bits, `widen` gives more
    bits, and a matrix product takes 8 bits and gives 32.
  * A Python `for` over a `range`, an `if` on an integer, a helper function,
    a list of words: all of it runs while tracing and leaves only the
    operations it called. `dense` below is such a helper.
  * A `tau.loop` is different: its body is traced once, with an index `i`
    that stands for every iteration. Positions and pins may depend on `i`,
    by `+`, `-` and `*` with integers only.
  * A kernel that calls another kernel is traced as a call.
  * `at=T + c` pins an operation: its word is issued on cycle `c`, counted
    from the start of its kernel. spec/Tau/Isa/Event.lean says what a pin claims.

The same function can also be run on real numbers (`run`), with the
operations computing instead of tracing. scripts/check-examples.sh compares
that run with what the Lean tools compute from the trace.

    python3 -m tau kernel.py -o out        write out/kernel.mlir, out/traced.json
    python3 -m tau kernel.py --run b.json  run on the buffers in b.json

`kernel.mlir` is the input of `tauc`. `traced.json` is the same program as a
source file (docs/Formats.md, section 1), written here without the compiler; `tauc`
writes its own from the MLIR, and the two must be equal.

Terms to look up: *embedded domain-specific language*, *tracing*,
*metaprogramming*.
"""

import inspect
import re

__all__ = [
    "Buf", "T", "kernel", "loop", "alloc", "trace", "run", "dense",
    "i8", "i16", "i32",
    "load", "store", "const", "select", "matvec", "widen",
    "relu", "neg", "abs", "reverse", "requant", "shl", "addi", "muli",
    "shift", "rotate", "broadcast", "permute",
    "add", "sub", "mul", "max", "min", "and_", "or_", "xor", "lt",
]


class TauError(Exception):
    """A program that cannot be traced."""


# ---------------------------------------------------------------------------
# Positions and pins
# ---------------------------------------------------------------------------

class Index:
    """A position that may depend on the iteration of a loop:
    `base + stride * i`. The index of a `tau.loop` is `Index(0, 1)`."""

    def __init__(self, base, stride):
        self.base = base
        self.stride = stride

    def __add__(self, other):
        if isinstance(other, int):
            return Index(self.base + other, self.stride)
        if isinstance(other, Index):
            return Index(self.base + other.base, self.stride + other.stride)
        return NotImplemented

    __radd__ = __add__

    def __sub__(self, other):
        if isinstance(other, int):
            return Index(self.base - other, self.stride)
        return NotImplemented

    def __mul__(self, other):
        if isinstance(other, int):
            return Index(self.base * other, self.stride * other)
        return NotImplemented

    __rmul__ = __mul__

    def __bool__(self):
        raise TauError("a loop index cannot be tested: the body of a tau.loop "
                       "is traced once, for every iteration")


class Time:
    """A cycle counted from the start of the kernel: `T + base + stride * i`."""

    def __init__(self, base, stride):
        self.base = base
        self.stride = stride

    def __add__(self, other):
        if isinstance(other, int):
            return Time(self.base + other, self.stride)
        if isinstance(other, Index):
            return Time(self.base + other.base, self.stride + other.stride)
        return NotImplemented

    __radd__ = __add__


T = Time(0, 0)
"""The cycle on which the kernel starts."""


def _position(pos):
    """A position as (base, stride)."""
    if isinstance(pos, int):
        pos = Index(pos, 0)
    if not isinstance(pos, Index):
        raise TauError("a position is an integer or a loop index")
    if pos.base < 0 or pos.stride < 0:
        raise TauError("a position cannot go below zero")
    if pos.stride and not _ctx.in_loop():
        raise TauError("a loop index was used outside its loop")
    return pos.base, pos.stride


def _pin(at):
    """A pin as (base, stride), or None."""
    if at is None:
        return None
    if not isinstance(at, Time):
        raise TauError("`at` takes a cycle written from T, such as T + 5")
    if at.base < 0 or at.stride < 0:
        raise TauError("a pin cannot go below cycle zero")
    if at.stride and not _ctx.in_loop():
        raise TauError("a loop index was used outside its loop")
    return at.base, at.stride


# ---------------------------------------------------------------------------
# Types, values and buffers
# ---------------------------------------------------------------------------

# A type is the number of bits of an element.
i8, i16, i32 = 8, 16, 32


def _type(bits):
    if bits not in (i8, i16, i32):
        raise TauError("a type is tau.i8, tau.i16 or tau.i32")
    return bits


def _name(bits):
    """The name of a type in a source file: "i8", "i16" or "i32"."""
    return f"i{bits}"


class Value:
    """One value of `bits` bits. While tracing it is a name; in a run it
    holds its elements. Either way Python cannot look inside it."""

    __slots__ = ("frame", "id", "bits", "lanes", "scope")

    def __init__(self, bits, frame=None, id=None, lanes=None, scope=None):
        self.bits = bits
        self.frame = frame
        self.id = id
        self.lanes = lanes
        self.scope = scope

    def __bool__(self):
        raise TauError("a value cannot be tested: a program cannot decide "
                       "anything from its data")

    __eq__ = object.__eq__
    __hash__ = object.__hash__


class Buffer:
    """A buffer of a kernel: `size` values of `bits` bits. `words` is its
    contents in a run, the elements of each value."""

    __slots__ = ("frame", "index", "size", "bits", "words")

    def __init__(self, frame, index, size, bits, words=None):
        self.frame = frame
        self.index = index
        self.size = size
        self.bits = bits
        self.words = words


class Buf:
    """The type of a kernel's buffer argument: `tau.Buf[4]` is four values of
    8 bits, and `tau.Buf[4, tau.i32]` four of 32. `tau.Buf["N"]` takes its
    size from the kernel's constant `N`."""

    def __init__(self, size, bits=i8):
        self.size = size
        self.bits = _type(bits)

    def __class_getitem__(cls, item):
        return cls(*item) if isinstance(item, tuple) else cls(item)


# ---------------------------------------------------------------------------
# Kernels
# ---------------------------------------------------------------------------

class Kernel:
    """A function marked `@tau.kernel`, with values for its constants.

    The positional parameters of the function are its buffers. Its
    keyword-only parameters are constants: integers fixed before tracing.
    `specialize` fixes them; so do keyword arguments at a call."""

    def __init__(self, fn, consts=None):
        self.fn = fn
        sig = inspect.signature(fn)
        self.params = []
        defaults = {}
        for p in sig.parameters.values():
            if p.kind == p.KEYWORD_ONLY:
                if p.default is not p.empty:
                    defaults[p.name] = p.default
            elif isinstance(p.annotation, Buf):
                self.params.append((p.annotation.size, p.annotation.bits))
            else:
                raise TauError(f"{fn.__name__}: parameter '{p.name}' needs "
                               "the type tau.Buf[size]")
        self.consts = {**defaults, **(consts or {})}

    def specialize(self, **consts):
        return Kernel(self.fn, {**self.consts, **consts})

    @property
    def name(self):
        parts = [self.fn.__name__]
        parts += [f"{k}_{v}" for k, v in sorted(self.consts.items())]
        # A name the compiler accepts: letters, digits and underscores.
        return re.sub(r"[^A-Za-z0-9_]+", "_", "__".join(parts)).strip("_")

    @property
    def sizes(self):
        """For each buffer, its size and the bits of its values."""
        return [(self.consts[s] if isinstance(s, str) else s, bits)
                for s, bits in self.params]

    def key(self):
        return (self.fn, tuple(sorted(self.consts.items())))

    def __call__(self, *buffers, at=None, **consts):
        if _ctx is None:
            raise TauError("a kernel is called from inside another kernel; "
                           "use tau.trace or tau.run on the outermost one")
        target = self.specialize(**consts) if consts else self
        _ctx.call(target, list(buffers), at)


def kernel(fn):
    """Mark a function as a kernel."""
    return Kernel(fn)


# ---------------------------------------------------------------------------
# Tracing
# ---------------------------------------------------------------------------

class _Def:
    """One traced kernel: the sizes and types of its buffers and its items.
    An item is a statement, a loop or a call, as in a source file."""

    def __init__(self, name, sizes):
        self.name = name
        self.sizes = list(sizes)
        self.items = []
        self.values = 0


class _Tracer:
    """Traces the operations a kernel calls."""

    def __init__(self):
        self.defs = {}       # Kernel.key() -> _Def, finished kernels
        self.order = []      # finished kernels, callees first
        self.frames = []     # kernels being traced, outermost first
        self.loop = None     # the items of the open loop, or None
        self.scope = 0       # counts loops, so that a word knows its own

    def in_loop(self):
        return self.loop is not None

    def trace(self, target):
        frame = _Def(target.name, target.sizes)
        saved = self.loop, self.scope
        self.loop = None
        self.frames.append(frame)
        buffers = [Buffer(frame, i, n, bits)
                   for i, (n, bits) in enumerate(frame.sizes)]
        target.fn(*buffers, **target.consts)
        if self.loop is not None:
            raise TauError("a tau.loop was not finished")
        self.frames.pop()
        self.loop, self.scope = saved
        names = {d.name for d in self.order}
        while frame.name in names:
            frame.name += "_"
        self.order.append(frame)
        return frame

    def emit(self, item):
        (self.loop if self.loop is not None else self.frames[-1].items).append(item)

    def buffer(self, buf):
        if not isinstance(buf, Buffer) or buf.frame is not self.frames[-1]:
            raise TauError("not a buffer of this kernel")
        return buf.index

    def use(self, value, bits=None):
        if not isinstance(value, Value) or value.frame is not self.frames[-1]:
            raise TauError("not a value of this kernel")
        if value.scope is not None and value.scope != (self.scope if self.in_loop() else None):
            raise TauError("a value made inside a tau.loop cannot be used "
                           "outside it")
        if bits is not None and value.bits != bits:
            raise TauError(f"a value of {value.bits} bits where one of "
                           f"{bits} bits is needed")
        return value.id

    def define(self, bits):
        frame = self.frames[-1]
        value = Value(bits, frame, frame.values,
                      scope=self.scope if self.in_loop() else None)
        frame.values += 1
        return value

    def stmt(self, op, fields, operands, pin, result=None, bits=None):
        """Trace one statement. `bits` is the type its operands have to have,
        and `result` the type of the value it gives, if it gives one."""
        item = {"op": op}
        for key, value in operands:
            item[key] = self.use(value, bits)
        item.update(fields)
        value = None
        if result is not None:
            value = self.define(result)
            item["dst"] = value.id
        if pin is not None:
            item["at"] = pin[0]
            if pin[1]:
                item["every"] = pin[1]
        self.emit(item)
        return value

    def begin_loop(self, n):
        if self.loop is not None:
            raise TauError("a tau.loop cannot be inside another")
        self.scope += 1
        self.loop = []

    def end_loop(self, n):
        body, self.loop = self.loop, None
        self.emit({"op": "loop", "n": n, "body": body})

    def alloc(self, size, bits):
        if len(self.frames) != 1:
            raise TauError("tau.alloc belongs in the outermost kernel")
        frame = self.frames[0]
        frame.sizes.append((size, bits))
        return Buffer(frame, len(frame.sizes) - 1, size, bits)

    def call(self, target, buffers, at):
        if self.loop is not None:
            raise TauError("a kernel cannot be called inside a tau.loop")
        pin = _pin(at)
        args = [self.buffer(b) for b in buffers]
        if len(set(args)) != len(args):
            raise TauError(f"{target.name}: a buffer is passed twice")
        if [(b.size, b.bits) for b in buffers] != target.sizes:
            raise TauError(f"{target.name}: expected buffers of sizes and "
                           f"bits {target.sizes}")
        if target.key() not in self.defs:
            self.defs[target.key()] = self.trace(target)
        self.emit({"op": "call", "args": args, "at": pin[0] if pin else 0,
                   "def": self.defs[target.key()]})


class Program:
    """A traced program: the outermost kernel and the kernels it calls."""

    def __init__(self, entry, order):
        self.entry = entry
        self.order = order

    def source(self):
        """The program as a source file (docs/Formats.md, section 1)."""
        def body(items):
            out = []
            for item in items:
                if item["op"] == "loop":
                    out.append({**item, "body": body(item["body"])})
                elif item["op"] == "call":
                    out.append({"op": "call", "args": item["args"],
                                "at": item["at"],
                                "body": body(item["def"].items)})
                else:
                    out.append(dict(item))
            return out
        # A buffer is a row of words: a value of `bits` bits is `bits / 8` of
        # them (Programs 1).
        words = [size * bits // 8 for size, bits in self.entry.sizes]
        return {"buffers": words, "body": body(self.entry.items)}

    def mlir(self):
        """The program in the `tau` dialect, the input of `tauc`."""
        return "\n".join(_mlir_function(d) for d in self.order)


def _mlir_function(d):
    def buf(i):
        return f"%b{i}"

    def ty(i):
        return f"!tau.buf<{d.sizes[i][0]} x {d.sizes[i][1]}>"

    def val(name):
        return f"!tau.int<{name[1:]}>"

    def stmt(item):
        op = item["op"]
        pin = ""
        if "at" in item:
            pin = f" at {item['at']}"
            if item.get("every"):
                pin += f" every {item['every']}"
        at = f"[{item.get('base', 0)}, {item.get('stride', 0)}]"
        if op == "load":
            return (f"%v{item['dst']} = tau.load {buf(item['buf'])}{at}{pin}"
                    f" : {ty(item['buf'])}")
        if op == "store":
            return (f"tau.store %v{item['src']}, {buf(item['buf'])}{at}{pin}"
                    f" : {ty(item['buf'])}")
        if op == "un":
            extra = ""
            if "k" in item:
                extra = f", {item['k']}"
            if "table" in item:
                extra = f", {item['table']}"
            to = f" to {val(item['to'])}" if "to" in item else ""
            return (f"%v{item['dst']} = tau.{item['fn']} %v{item['a']}{extra}"
                    f"{pin} : {val(item['ty'])}{to}")
        if op == "bin":
            return (f"%v{item['dst']} = tau.{item['fn']} %v{item['a']}, "
                    f"%v{item['b']}{pin} : {val(item['ty'])}")
        if op == "const":
            return (f"%v{item['dst']} = tau.const {item['values']}{pin}"
                    f" : {val(item['ty'])}")
        if op == "sel":
            return (f"%v{item['dst']} = tau.select %v{item['m']}, "
                    f"%v{item['a']}, %v{item['b']}{pin} : {val(item['ty'])}")
        if op == "matvec":
            return (f"%v{item['dst']} = tau.matvec %v{item['x']}, "
                    f"{buf(item['buf'])}{at}, {item['n']}{pin} : {ty(item['buf'])}")
        raise TauError(f"cannot write '{op}'")

    lines = []
    args = ", ".join(f"{buf(i)}: {ty(i)}" for i in range(len(d.sizes)))
    lines.append(f"func.func @{d.name}({args}) {{")
    for item in d.items:
        if item["op"] == "loop":
            lines.append(f"  tau.for {item['n']} {{")
            lines += ["    " + stmt(s) for s in item["body"]]
            lines.append("  }")
        elif item["op"] == "call":
            names = ", ".join(buf(a) for a in item["args"])
            types = ", ".join(ty(a) for a in item["args"])
            at = f" at {item['at']}" if item["at"] else ""
            lines.append(f"  tau.call @{item['def'].name}({names}){at} : ({types})")
        else:
            lines.append("  " + stmt(item))
    lines.append("  return")
    lines.append("}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Running on real numbers
# ---------------------------------------------------------------------------

def _wrap(v, bits=32):
    """A signed integer of `bits` bits: arithmetic wraps around. A slice
    computes with elements of 32 bits and keeps the low bytes of a result,
    as in spec/Tau/Isa/Word.lean; for the operations below that comes to
    computing with whole numbers and wrapping the result to its type."""
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


def _requant(k, x):
    s = x >> k
    return -128 if s < -128 else 127 if s > 127 else s


# What each one-value operation does to the elements of a value. The result
# is wrapped to its type afterwards.
_UN = {
    "relu": lambda k, w: [x if x >= 0 else 0 for x in w],
    "neg": lambda k, w: [-x for x in w],
    "abs": lambda k, w: [-x if x < 0 else x for x in w],
    "reverse": lambda k, w: w[::-1],
    "requant": lambda k, w: [_requant(k, x) for x in w],
    "shl": lambda k, w: [_wrap(x << k) for x in w],
    "addi": lambda k, w: [_wrap(x + _wrap(k)) for x in w],
    "muli": lambda k, w: [_wrap(x * _wrap(k)) for x in w],
    "widen": lambda k, w: list(w),
    "shift": lambda k, w: [w[i - k] if k <= i else 0 for i in range(len(w))],
    "rotate": lambda k, w: [w[(i + k) % len(w)] for i in range(len(w))],
    "broadcast": lambda k, w: [w[k] if k < len(w) else 0 for _ in w],
    "permute": lambda t, w: [w[t[i]] if i < len(t) and t[i] < len(w) else 0
                             for i in range(len(w))],
}

_BIN = {
    "add": lambda a, b: a + b,
    "sub": lambda a, b: a - b,
    "mul": lambda a, b: a * b,
    "max": lambda a, b: b if a < b else a,
    "min": lambda a, b: a if a < b else b,
    "and": lambda a, b: a & b,
    "or": lambda a, b: a | b,
    "xor": lambda a, b: a ^ b,
    "lt": lambda a, b: 1 if a < b else 0,
}


class _Runner:
    """Computes the operations a kernel calls, on real words."""

    def __init__(self, lanes):
        self.lanes = lanes
        self.depth = 0
        self.origin = 0
        self.iteration = None
        self.events = []
        self.buffers = []
        self.types = []

    def in_loop(self):
        return self.iteration is not None

    def issue(self, pin, value, store=None):
        """The events of a pinned value: one for each of its words, the low
        byte of every element first. The words of a store go to the words
        of the buffer from the value's first word on."""
        if pin is None:
            return
        time = self.origin + pin[0] + pin[1] * (self.iteration or 0)
        count = value.bits // 8
        for k in range(count):
            word = [_wrap(x >> (8 * k), 8) for x in value.lanes]
            where = {"buf": store[0], "pos": count * store[1] + k} if store else {}
            self.events.append({"time": time, "word": word, **where})

    def value(self, bits, lanes, pin, store=None):
        """A value of a run, with its elements wrapped to its type."""
        value = Value(bits, lanes=[_wrap(x, bits) for x in lanes])
        self.issue(pin, value, store)
        return value

    def word(self, buf, pos):
        base, stride = pos
        k = base + stride * (self.iteration or 0)
        if k >= buf.size:
            raise TauError("a position outside its buffer")
        return k

    def alloc(self, size, bits):
        if self.depth != 1:
            raise TauError("tau.alloc belongs in the outermost kernel")
        words = [[0] * self.lanes for _ in range(size)]
        self.buffers.append(words)
        self.types.append(bits)
        return Buffer(None, len(self.buffers) - 1, size, bits, words)

    def call(self, target, buffers, at):
        pin = _pin(at)
        if self.in_loop():
            raise TauError("a kernel cannot be called inside a tau.loop")
        if len({id(b) for b in buffers}) != len(buffers):
            raise TauError(f"{target.name}: a buffer is passed twice")
        if [(b.size, b.bits) for b in buffers] != target.sizes:
            raise TauError(f"{target.name}: expected buffers of sizes and "
                           f"bits {target.sizes}")
        saved = self.origin
        self.origin += pin[0] if pin else 0
        self.depth += 1
        # The called kernel numbers its buffers from zero.
        inner = [Buffer(None, (i, b), b.size, b.bits, b.words)
                 for i, b in enumerate(buffers)]
        target.fn(*inner, **target.consts)
        self.depth -= 1
        self.origin = saved


def _outer(buf):
    """The number of a buffer in the outermost kernel: a called kernel's
    buffer stands for the caller's."""
    index = buf.index
    while isinstance(index, tuple):
        index = index[1].index
    return index


_ctx = None


def trace(target):
    """Trace a kernel and the kernels it calls."""
    global _ctx
    if _ctx is not None:
        raise TauError("tau.trace cannot be used inside a kernel")
    _ctx = tracer = _Tracer()
    try:
        entry = tracer.trace(target)
    finally:
        _ctx = None
    return Program(entry, tracer.order)


def run(target, buffers, lanes):
    """Run a kernel on real numbers. `buffers` holds, for each buffer, its
    type and its values as lists of integers (docs/Formats.md, section 6).
    Returns the final buffers in the same way, scratch buffers after the
    kernel's own, and the events of the pinned operations."""
    global _ctx
    if _ctx is not None:
        raise TauError("tau.run cannot be used inside a kernel")
    given = [(len(b["values"]), int(b["type"][1:])) for b in buffers]
    if given != target.sizes:
        raise TauError(f"{target.name}: expected buffers of sizes and bits "
                       f"{target.sizes}")
    _ctx = runner = _Runner(lanes)
    try:
        runner.types = [bits for _, bits in given]
        runner.buffers = [[[_wrap(x, bits) for x in (w + [0] * lanes)[:lanes]]
                           for w in b["values"]]
                          for b, bits in zip(buffers, runner.types)]
        runner.depth = 1
        handles = [Buffer(None, i, len(b), bits, b)
                   for i, (b, bits) in enumerate(zip(runner.buffers, runner.types))]
        target.fn(*handles, **target.consts)
    finally:
        _ctx = None
    out = [{"type": _name(bits), "values": b}
           for b, bits in zip(runner.buffers, runner.types)]
    return out, runner.events


# ---------------------------------------------------------------------------
# The operations
# ---------------------------------------------------------------------------

def _need():
    if _ctx is None:
        raise TauError("an operation is called from inside a kernel; use "
                       "tau.trace or tau.run on the kernel")
    return _ctx


def loop(n):
    """`for i in tau.loop(n):` runs its body for i = 0 .. n - 1. The body is
    traced once; `i` may be used in positions and pins."""
    ctx = _need()
    if isinstance(ctx, _Tracer):
        ctx.begin_loop(n)
        yield Index(0, 1)
        ctx.end_loop(n)
    else:
        if ctx.in_loop():
            raise TauError("a tau.loop cannot be inside another")
        for k in range(n):
            ctx.iteration = k
            # The index is the same handle as when tracing; the runner
            # fills in the iteration when a position or a pin is used.
            yield Index(0, 1)
        ctx.iteration = None


def alloc(size, bits=i8):
    """A scratch buffer of `size` values of `bits` bits, for one kernel to
    leave a result in and another to pick it up. It becomes a buffer of the
    program, after the outermost kernel's own, and starts as zeros."""
    return _need().alloc(size, _type(bits))


def load(buf, pos, at=None):
    """The value at position `pos` of `buf`."""
    ctx, at, pos = _need(), _pin(at), _position(pos)
    if isinstance(ctx, _Tracer):
        return ctx.stmt("load", {"ty": _name(buf.bits), "buf": ctx.buffer(buf),
                                 "base": pos[0], "stride": pos[1]}, [], at,
                        result=buf.bits)
    return ctx.value(buf.bits, buf.words[ctx.word(buf, pos)], at)


def store(buf, pos, value, at=None):
    """Store `value` at position `pos` of `buf`."""
    ctx, at, pos = _need(), _pin(at), _position(pos)
    if isinstance(ctx, _Tracer):
        ctx.stmt("store", {"ty": _name(buf.bits), "buf": ctx.buffer(buf),
                           "base": pos[0], "stride": pos[1]},
                 [("src", value)], at, bits=buf.bits)
        return
    if value.bits != buf.bits:
        raise TauError(f"a value of {value.bits} bits stored to a buffer of "
                       f"values of {buf.bits} bits")
    k = ctx.word(buf, pos)
    buf.words[k] = list(value.lanes)
    ctx.issue(at, value, store=(_outer(buf), k))


def const(values, bits=i8, at=None):
    """The value of `bits` bits with the given elements. Missing elements are
    zero."""
    ctx, at = _need(), _pin(at)
    values = [int(v) for v in values]
    if isinstance(ctx, _Tracer):
        return ctx.stmt("const", {"ty": _name(_type(bits)), "values": values},
                        [], at, result=bits)
    return ctx.value(_type(bits), (values + [0] * ctx.lanes)[:ctx.lanes], at)


def select(m, a, b, at=None):
    """Element by element: `a` where `m` is not zero, `b` elsewhere."""
    ctx, at = _need(), _pin(at)
    if isinstance(ctx, _Tracer):
        return ctx.stmt("sel", {"ty": _name(a.bits)},
                        [("m", m), ("a", a), ("b", b)], at,
                        result=a.bits, bits=a.bits)
    if not m.bits == a.bits == b.bits:
        raise TauError("tau.select takes three values of one type")
    lanes = [x if c != 0 else y for c, x, y in zip(m.lanes, a.lanes, b.lanes)]
    return ctx.value(a.bits, lanes, at)


def matvec(x, buf, pos, n, at=None):
    """The matrix whose `n` rows are the values of `buf` from `pos` on, times
    the value `x`: element `i` of the result is the dot product of row `i`
    with `x`, and the elements from `n` on are zero. The rows and `x` have 8
    bits and the result has 32."""
    ctx, at, pos = _need(), _pin(at), _position(pos)
    if buf.bits != i8:
        raise TauError("a matrix is in a buffer of values of 8 bits")
    if isinstance(ctx, _Tracer):
        return ctx.stmt("matvec", {"buf": ctx.buffer(buf), "base": pos[0],
                                   "stride": pos[1], "n": n}, [("x", x)], at,
                        result=i32, bits=i8)
    if x.bits != i8:
        raise TauError("a matrix is multiplied by a value of 8 bits")
    first = ctx.word(buf, pos)
    if first + n > buf.size:
        raise TauError("a matrix row outside its buffer")
    lanes = [0] * ctx.lanes
    for i in range(n):
        if i == ctx.lanes:
            break
        lanes[i] = sum(w * v for w, v in zip(buf.words[first + i], x.lanes))
    return ctx.value(i32, lanes, at)


def _unary(fn, takes):
    def op(a, *params, at=None):
        ctx, pin = _need(), _pin(at)
        if len(params) != (1 if takes else 0):
            raise TauError(f"tau.{fn} takes a value" +
                           (f" and `{takes}`" if takes else ""))
        param = params[0] if takes else None
        if takes == "table":
            param = [int(k) for k in param]
        # `requant` gives 8 bits and `widen` the bits it is told; any other
        # operation gives the type it takes.
        bits = i8 if fn == "requant" else _type(param) if fn == "widen" else a.bits
        if fn == "widen" and bits < a.bits:
            raise TauError(f"tau.widen of {a.bits} bits to {bits}")
        if isinstance(ctx, _Tracer):
            fields = {"fn": fn, "ty": _name(a.bits)}
            if fn == "widen":
                fields["to"] = _name(bits)
            elif takes:
                fields[takes] = param
            return ctx.stmt("un", fields, [("a", a)], pin, result=bits)
        return ctx.value(bits, _UN[fn](param, a.lanes), pin)
    op.__name__ = fn
    return op


def _binary(fn):
    def op(a, b, at=None):
        ctx, pin = _need(), _pin(at)
        if isinstance(ctx, _Tracer):
            return ctx.stmt("bin", {"fn": fn, "ty": _name(a.bits)},
                            [("a", a), ("b", b)], pin,
                            result=a.bits, bits=a.bits)
        if a.bits != b.bits:
            raise TauError(f"tau.{fn} takes two values of one type")
        lanes = [_BIN[fn](x, y) for x, y in zip(a.lanes, b.lanes)]
        return ctx.value(a.bits, lanes, pin)
    op.__name__ = fn
    return op


# One-value operations. The first group runs on a vector slice, the second on
# a rearrangement slice.
relu = _unary("relu", None)
widen = _unary("widen", "to")
neg = _unary("neg", None)
requant = _unary("requant", "k")
shl = _unary("shl", "k")
addi = _unary("addi", "k")
muli = _unary("muli", "k")

reverse = _unary("reverse", None)
shift = _unary("shift", "k")
rotate = _unary("rotate", "k")
broadcast = _unary("broadcast", "k")
permute = _unary("permute", "table")

# Two-value operations.
add = _binary("add")
sub = _binary("sub")
mul = _binary("mul")
and_ = _binary("and")
or_ = _binary("or")
xor = _binary("xor")
lt = _binary("lt")


def dense(x, weights, pos, n, bias=None, shift=0, activate=True, at=None):
    """A quantized linear layer: `relu(requant(W * x + bias, shift))`.

    `x` and the rows of `weights` have 8 bits, `bias` has 32 and the result
    8. This is not an operation of the machine. It is a Python function that
    calls three or four of them, and those are what gets traced. A pin
    given here goes on the matrix product."""
    y = matvec(x, weights, pos, n, at=at)
    if bias is not None:
        y = add(y, bias)
    y = requant(y, shift)
    return relu(y) if activate else y


# These three are named after Python's own functions, so they come last:
# nothing above may use them by their short names.
abs = _unary("abs", None)
max = _binary("max")
min = _binary("min")
