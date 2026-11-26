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
calls is recorded. What is recorded is a source program: `Source` in
Tau/IR/Source.lean says what it computes and when. So Python is the language
the program is written with, and the record is the program.

What follows from that:

  * A word is a handle with no operators. Python cannot add two words or
    test one, so what a program does cannot depend on its data. That is the
    property the machine has, and the one every check rests on.
  * A Python `for` over a `range`, an `if` on an integer, a helper function,
    a list of words: all of it runs while recording and leaves only the
    operations it called. `dense` below is such a helper.
  * A `tau.loop` is different: its body is recorded once, with an index `i`
    that stands for every iteration. Positions and pins may depend on `i`,
    by `+`, `-` and `*` with integers only.
  * A kernel that calls another kernel is recorded as a call.
  * `at=T + c` pins an operation: its word is issued on cycle `c`, counted
    from the start of its kernel. Tau/Isa/Event.lean says what a pin claims.

The same function can also be run on real numbers (`run`), with the
operations computing instead of recording. scripts/check-examples.sh compares
that run with what the Lean tools compute from the record.

    python3 -m tau kernel.py -o out        write out/kernel.mlir, out/traced.json
    python3 -m tau kernel.py --run b.json  run on the buffers in b.json

`kernel.mlir` is the input of `tauc`. `traced.json` is the same program as a
source file (Tau/Docs/Formats.md, section 1), written here without the compiler; `tauc`
writes its own from the MLIR, and the two must be equal.

Terms to look up: *embedded domain-specific language*, *tracing*,
*metaprogramming*.
"""

import inspect
import re

__all__ = [
    "Buf", "T", "kernel", "loop", "alloc", "trace", "run", "dense",
    "load", "store", "const", "select", "matvec", "affine",
    "relu", "neg", "abs", "reverse", "requant", "shl", "addi", "muli",
    "shift", "rotate", "broadcast", "permute",
    "add", "sub", "mul", "max", "min", "and_", "or_", "xor", "lt",
]


class TauError(Exception):
    """A program that cannot be recorded."""


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
                       "is recorded once, for every iteration")


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
# Words and buffers
# ---------------------------------------------------------------------------

class Word:
    """One word. While recording it is a name; in a run it holds lanes.
    Either way Python cannot look inside it."""

    __slots__ = ("frame", "id", "lanes", "scope")

    def __init__(self, frame=None, id=None, lanes=None, scope=None):
        self.frame = frame
        self.id = id
        self.lanes = lanes
        self.scope = scope

    def __bool__(self):
        raise TauError("a word cannot be tested: a program cannot decide "
                       "anything from its data")

    __eq__ = object.__eq__
    __hash__ = object.__hash__


class Buffer:
    """A buffer of a kernel. `words` is its contents in a run."""

    __slots__ = ("frame", "index", "size", "words")

    def __init__(self, frame, index, size, words=None):
        self.frame = frame
        self.index = index
        self.size = size
        self.words = words


class Buf:
    """The type of a kernel's buffer argument: `tau.Buf[4]` is four words.
    `tau.Buf["N"]` takes its size from the kernel's constant `N`."""

    def __init__(self, size):
        self.size = size

    def __class_getitem__(cls, size):
        return cls(size)


# ---------------------------------------------------------------------------
# Kernels
# ---------------------------------------------------------------------------

class Kernel:
    """A function marked `@tau.kernel`, with values for its constants.

    The positional parameters of the function are its buffers. Its
    keyword-only parameters are constants: integers fixed before recording.
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
                self.params.append(p.annotation.size)
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
        return [self.consts[s] if isinstance(s, str) else s
                for s in self.params]

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
# Recording
# ---------------------------------------------------------------------------

class _Def:
    """One recorded kernel: the sizes of its buffers and its items. An item
    is a statement, a loop or a call, as in a source file."""

    def __init__(self, name, sizes):
        self.name = name
        self.sizes = list(sizes)
        self.items = []
        self.values = 0


class _Tracer:
    """Records the operations a kernel calls."""

    def __init__(self):
        self.defs = {}       # Kernel.key() -> _Def, finished kernels
        self.order = []      # finished kernels, callees first
        self.frames = []     # kernels being recorded, outermost first
        self.loop = None     # the items of the open loop, or None
        self.scope = 0       # counts loops, so that a word knows its own

    def in_loop(self):
        return self.loop is not None

    def record(self, target):
        frame = _Def(target.name, target.sizes)
        saved = self.loop, self.scope
        self.loop = None
        self.frames.append(frame)
        buffers = [Buffer(frame, i, n) for i, n in enumerate(frame.sizes)]
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

    def use(self, word):
        if not isinstance(word, Word) or word.frame is not self.frames[-1]:
            raise TauError("not a word of this kernel")
        if word.scope is not None and word.scope != (self.scope if self.in_loop() else None):
            raise TauError("a word made inside a tau.loop cannot be used "
                           "outside it")
        return word.id

    def define(self):
        frame = self.frames[-1]
        word = Word(frame, frame.values, scope=self.scope if self.in_loop() else None)
        frame.values += 1
        return word

    def stmt(self, op, fields, operands, pin, result=True):
        item = {"op": op}
        for key, word in operands:
            item[key] = self.use(word)
        item.update(fields)
        word = None
        if result:
            word = self.define()
            item["dst"] = word.id
        if pin is not None:
            item["at"] = pin[0]
            if pin[1]:
                item["every"] = pin[1]
        self.emit(item)
        return word

    def begin_loop(self, n):
        if self.loop is not None:
            raise TauError("a tau.loop cannot be inside another")
        self.scope += 1
        self.loop = []

    def end_loop(self, n):
        body, self.loop = self.loop, None
        self.emit({"op": "loop", "n": n, "body": body})

    def alloc(self, size):
        if len(self.frames) != 1:
            raise TauError("tau.alloc belongs in the outermost kernel")
        frame = self.frames[0]
        frame.sizes.append(size)
        return Buffer(frame, len(frame.sizes) - 1, size)

    def call(self, target, buffers, at):
        if self.loop is not None:
            raise TauError("a kernel cannot be called inside a tau.loop")
        pin = _pin(at)
        args = [self.buffer(b) for b in buffers]
        if len(set(args)) != len(args):
            raise TauError(f"{target.name}: a buffer is passed twice")
        if [b.size for b in buffers] != target.sizes:
            raise TauError(f"{target.name}: expected buffers of sizes "
                           f"{target.sizes}")
        if target.key() not in self.defs:
            self.defs[target.key()] = self.record(target)
        self.emit({"op": "call", "args": args, "at": pin[0] if pin else 0,
                   "def": self.defs[target.key()]})


class Program:
    """A recorded program: the outermost kernel and the kernels it calls."""

    def __init__(self, entry, order):
        self.entry = entry
        self.order = order

    def source(self):
        """The program as a source file (Tau/Docs/Formats.md, section 1)."""
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
        return {"buffers": self.entry.sizes, "body": body(self.entry.items)}

    def mlir(self):
        """The program in the `tau` dialect, the input of `tauc`."""
        return "\n".join(_mlir_function(d) for d in self.order)


def _mlir_function(d):
    def buf(i):
        return f"%b{i}"

    def ty(i):
        return f"!tau.buf<{d.sizes[i]}>"

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
            return f"%v{item['dst']} = tau.{item['fn']} %v{item['a']}{extra}{pin}"
        if op == "bin":
            return (f"%v{item['dst']} = tau.{item['fn']} %v{item['a']}, "
                    f"%v{item['b']}{pin}")
        if op == "const":
            return f"%v{item['dst']} = tau.const {item['values']}{pin}"
        if op == "sel":
            return (f"%v{item['dst']} = tau.select %v{item['m']}, "
                    f"%v{item['a']}, %v{item['b']}{pin}")
        if op == "matvec":
            return (f"%v{item['dst']} = tau.matvec %v{item['x']}, "
                    f"{buf(item['buf'])}{at}, {item['n']}{pin} : {ty(item['buf'])}")
        if op == "affine":
            return (f"%v{item['dst']} = tau.affine %v{item['x']}, "
                    f"{buf(item['buf'])}{at}, {item['n']}, %v{item['bias']}{pin}"
                    f" : {ty(item['buf'])}")
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

def _wrap(v):
    """A 32-bit signed lane: arithmetic wraps around, as in Tau/Data/Word.lean."""
    v &= 0xFFFFFFFF
    return v - (1 << 32) if v & 0x80000000 else v


def _requant(k, x):
    s = x >> k
    return -128 if s < -128 else 127 if s > 127 else s


_UN = {
    "relu": lambda k, w: [x if x >= 0 else 0 for x in w],
    "neg": lambda k, w: [_wrap(-x) for x in w],
    "abs": lambda k, w: [_wrap(-x) if x < 0 else x for x in w],
    "reverse": lambda k, w: w[::-1],
    "requant": lambda k, w: [_requant(k, x) for x in w],
    "shl": lambda k, w: [_wrap(x << k) for x in w],
    "addi": lambda k, w: [_wrap(x + k) for x in w],
    "muli": lambda k, w: [_wrap(x * k) for x in w],
    "shift": lambda k, w: [w[i - k] if k <= i else 0 for i in range(len(w))],
    "rotate": lambda k, w: [w[(i + k) % len(w)] for i in range(len(w))],
    "broadcast": lambda k, w: [w[k] if k < len(w) else 0 for _ in w],
    "permute": lambda t, w: [w[t[i]] if i < len(t) and t[i] < len(w) else 0
                             for i in range(len(w))],
}

_BIN = {
    "add": lambda a, b: _wrap(a + b),
    "sub": lambda a, b: _wrap(a - b),
    "mul": lambda a, b: _wrap(a * b),
    "max": lambda a, b: b if a < b else a,
    "min": lambda a, b: a if a < b else b,
    "and": lambda a, b: _wrap(a & b),
    "or": lambda a, b: _wrap(a | b),
    "xor": lambda a, b: _wrap(a ^ b),
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

    def in_loop(self):
        return self.iteration is not None

    def issue(self, pin, lanes, store=None):
        if pin is not None:
            time = self.origin + pin[0] + pin[1] * (self.iteration or 0)
            self.events.append({"time": time, "word": list(lanes),
                                **({"buf": store[0], "pos": store[1]} if store else {})})

    def word(self, buf, pos):
        base, stride = pos
        k = base + stride * (self.iteration or 0)
        if k >= buf.size:
            raise TauError("a position outside its buffer")
        return k

    def alloc(self, size):
        if self.depth != 1:
            raise TauError("tau.alloc belongs in the outermost kernel")
        words = [[0] * self.lanes for _ in range(size)]
        self.buffers.append(words)
        return Buffer(None, len(self.buffers) - 1, size, words)

    def call(self, target, buffers, at):
        pin = _pin(at)
        if self.in_loop():
            raise TauError("a kernel cannot be called inside a tau.loop")
        if len({id(b) for b in buffers}) != len(buffers):
            raise TauError(f"{target.name}: a buffer is passed twice")
        if [b.size for b in buffers] != target.sizes:
            raise TauError(f"{target.name}: expected buffers of sizes "
                           f"{target.sizes}")
        saved = self.origin
        self.origin += pin[0] if pin else 0
        self.depth += 1
        # The called kernel numbers its buffers from zero.
        inner = [Buffer(None, (i, b), b.size, b.words) for i, b in enumerate(buffers)]
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
    """Record a kernel and the kernels it calls."""
    global _ctx
    if _ctx is not None:
        raise TauError("tau.trace cannot be used inside a kernel")
    _ctx = tracer = _Tracer()
    try:
        entry = tracer.record(target)
    finally:
        _ctx = None
    return Program(entry, tracer.order)


def run(target, buffers, lanes):
    """Run a kernel on real numbers. `buffers` holds, for each buffer, its
    words as lists of integers. Returns the final buffers, scratch buffers
    after the kernel's own, and the events of the pinned operations."""
    global _ctx
    if _ctx is not None:
        raise TauError("tau.run cannot be used inside a kernel")
    if [len(b) for b in buffers] != target.sizes:
        raise TauError(f"{target.name}: expected buffers of sizes {target.sizes}")
    _ctx = runner = _Runner(lanes)
    try:
        runner.buffers = [[[_wrap(x) for x in (w + [0] * lanes)[:lanes]] for w in b]
                          for b in buffers]
        runner.depth = 1
        handles = [Buffer(None, i, len(b), b) for i, b in enumerate(runner.buffers)]
        target.fn(*handles, **target.consts)
    finally:
        _ctx = None
    return runner.buffers, runner.events


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
    recorded once; `i` may be used in positions and pins."""
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
            # The index is the same handle as when recording; the runner
            # fills in the iteration when a position or a pin is used.
            yield Index(0, 1)
        ctx.iteration = None


def alloc(size):
    """A scratch buffer of `size` words, for one kernel to leave a result in
    and another to pick it up. It becomes a buffer of the program, after the
    outermost kernel's own, and starts as zeros."""
    return _need().alloc(size)


def load(buf, pos, at=None):
    """The word at position `pos` of `buf`."""
    ctx, at, pos = _need(), _pin(at), _position(pos)
    if isinstance(ctx, _Tracer):
        return ctx.stmt("load", {"buf": ctx.buffer(buf), "base": pos[0],
                                 "stride": pos[1]}, [], at)
    lanes = list(buf.words[ctx.word(buf, pos)])
    ctx.issue(at, lanes)
    return Word(lanes=lanes)


def store(buf, pos, word, at=None):
    """Store `word` at position `pos` of `buf`."""
    ctx, at, pos = _need(), _pin(at), _position(pos)
    if isinstance(ctx, _Tracer):
        ctx.stmt("store", {"buf": ctx.buffer(buf), "base": pos[0],
                           "stride": pos[1]}, [("src", word)], at, result=False)
        return
    k = ctx.word(buf, pos)
    buf.words[k] = list(word.lanes)
    ctx.issue(at, word.lanes, store=(_outer(buf), k))


def const(values, at=None):
    """The word with the given lanes. Missing lanes are zero."""
    ctx, at = _need(), _pin(at)
    values = [int(v) for v in values]
    if isinstance(ctx, _Tracer):
        return ctx.stmt("const", {"values": values}, [], at)
    lanes = [_wrap(v) for v in (values + [0] * ctx.lanes)[:ctx.lanes]]
    ctx.issue(at, lanes)
    return Word(lanes=lanes)


def select(m, a, b, at=None):
    """Lane by lane: `a` where `m` is not zero, `b` elsewhere."""
    ctx, at = _need(), _pin(at)
    if isinstance(ctx, _Tracer):
        return ctx.stmt("sel", {}, [("m", m), ("a", a), ("b", b)], at)
    lanes = [x if c != 0 else y for c, x, y in zip(m.lanes, a.lanes, b.lanes)]
    ctx.issue(at, lanes)
    return Word(lanes=lanes)


def _product(ctx, x, buf, pos, n, start):
    acc = list(start)
    first = ctx.word(buf, pos)
    for j in range(n):
        if first + j >= buf.size:
            raise TauError("a matrix column outside its buffer")
        scale = x.lanes[j] if j < ctx.lanes else 0
        acc = [_wrap(a + scale * c) for a, c in zip(acc, buf.words[first + j])]
    return acc


def matvec(x, buf, pos, n, at=None):
    """The matrix whose `n` columns are the words of `buf` from `pos` on,
    times the word `x`."""
    ctx, at, pos = _need(), _pin(at), _position(pos)
    if isinstance(ctx, _Tracer):
        return ctx.stmt("matvec", {"buf": ctx.buffer(buf), "base": pos[0],
                                   "stride": pos[1], "n": n}, [("x", x)], at)
    lanes = _product(ctx, x, buf, pos, n, [0] * ctx.lanes)
    ctx.issue(at, lanes)
    return Word(lanes=lanes)


def affine(x, buf, pos, n, bias, at=None):
    """As `matvec`, with the word `bias` added."""
    ctx, at, pos = _need(), _pin(at), _position(pos)
    if isinstance(ctx, _Tracer):
        return ctx.stmt("affine", {"buf": ctx.buffer(buf), "base": pos[0],
                                   "stride": pos[1], "n": n},
                        [("x", x), ("bias", bias)], at)
    lanes = _product(ctx, x, buf, pos, n, bias.lanes)
    ctx.issue(at, lanes)
    return Word(lanes=lanes)


def _unary(fn, takes):
    def op(a, *params, at=None):
        ctx, pin = _need(), _pin(at)
        if len(params) != (1 if takes else 0):
            raise TauError(f"tau.{fn} takes a word" +
                           (f" and `{takes}`" if takes else ""))
        param = params[0] if takes else None
        if takes == "table":
            param = [int(k) for k in param]
        if isinstance(ctx, _Tracer):
            return ctx.stmt("un", {"fn": fn, **({takes: param} if takes else {})},
                            [("a", a)], pin)
        lanes = _UN[fn](param, a.lanes)
        ctx.issue(pin, lanes)
        return Word(lanes=lanes)
    op.__name__ = fn
    return op


def _binary(fn):
    def op(a, b, at=None):
        ctx, pin = _need(), _pin(at)
        if isinstance(ctx, _Tracer):
            return ctx.stmt("bin", {"fn": fn}, [("a", a), ("b", b)], pin)
        lanes = [_BIN[fn](x, y) for x, y in zip(a.lanes, b.lanes)]
        ctx.issue(pin, lanes)
        return Word(lanes=lanes)
    op.__name__ = fn
    return op


# One-word operations. The first group runs on a vector slice, the second on
# a rearrangement slice.
relu = _unary("relu", None)
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

# Two-word operations.
add = _binary("add")
sub = _binary("sub")
mul = _binary("mul")
and_ = _binary("and")
or_ = _binary("or")
xor = _binary("xor")
lt = _binary("lt")


def dense(x, weights, pos, n, bias=None, shift=0, activate=True, at=None):
    """A quantized linear layer: `relu(requant(W * x + bias, shift))`.

    This is not an operation of the machine. It is a Python function that
    calls three or four of them, and those are what gets recorded. A pin
    given here goes on the matrix product."""
    if bias is None:
        y = matvec(x, weights, pos, n, at=at)
    else:
        y = affine(x, weights, pos, n, bias, at=at)
    y = requant(y, shift)
    return relu(y) if activate else y


# These three are named after Python's own functions, so they come last:
# nothing above may use them by their short names.
abs = _unary("abs", None)
max = _binary("max")
min = _binary("min")
