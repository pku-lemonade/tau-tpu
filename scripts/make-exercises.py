#!/usr/bin/env python3
"""Generate the proof exercises from the finished proofs.

The course asks for few proofs: the short ones that show what a
specification says. `EXERCISES` below lists them. Each listed file under
Tau/Proofs/ becomes a file under course/Exercises/ in which the listed
proofs are replaced by `sorry`. Statements, doc comments and imports are
kept, and so are the proofs that are not listed, which the student may use.
The finished file is the solution.

A file under Tau/Proofs/ that is not listed has no exercise file. Its proofs
are for reading.

A comment at the top level of a proof (two spaces, then `-- `) is kept in the
exercise as an outline. Write such comments in long proofs to say what each
part does.

    scripts/make-exercises.py           write course/Exercises/
    scripts/make-exercises.py --check   fail if course/Exercises/ is out of date

An exercise file imports the finished library, not other exercise files, so
each one can be done on its own.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE = ROOT / "Tau" / "Proofs"
TARGET = ROOT / "course" / "Exercises"

HEADER = """\
/-
Exercise file. Generated from {source} by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in {source}.
{given}Build this file alone with:

    lake build {module}
-/

"""

GIVEN = """\
Only some proofs are taken out. The others are given, and you may use them.
"""

DECL = re.compile(r"^(theorem|lemma)\s+(\S+)")

ALL = None

# Which proofs are exercises. A file maps to ALL, or to the names of the
# theorems whose proofs are taken out; the other proofs in that file stay.
EXERCISES: dict[str, set[str] | None] = {
    "Blocks/Basic.lean": ALL,
    "Blocks/ShiftRegister.lean": ALL,
    "Blocks/Accumulator.lean": ALL,
    "Blocks/Mac.lean": ALL,
    "Data/Lane.lean": ALL,
    "Blocks/Pipeline.lean": ALL,
    "Blocks/Sequencer.lean": ALL,
    "Blocks/Memory.lean": {"memory_outAt_read"},
    "Blocks/Repeater.lean": {"repeater_stateAt", "repeater_outAt"},
    "Blocks/SystolicArray.lean": {"systolicArray_matvec"},
    "Passes/Unroll.lean": {"Idx.eval_inst", "Stmt.exec_inst", "Kernel.run_unroll"},
    "Check/Simplify.lean": ALL,
    "Check/Sound.lean": {"check_sound", "check_pins", "check_safe"},
    "Check/Passes.lean": {"checkKernels_sound", "checkKernels_pins", "passes_sound",
                          "passes_pins"},
    "EndToEnd.lean": ALL,
}


def blank_proofs(text: str, only: set[str] | None) -> tuple[str, int]:
    """Replace the body of `theorem ... := by` with `sorry`: of every theorem
    if `only` is None, and otherwise of the theorems named in `only`."""
    lines = text.split("\n")
    out: list[str] = []
    count = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        decl = DECL.match(line)
        if not decl or (only is not None and decl.group(2) not in only):
            out.append(line)
            i += 1
            continue

        # Copy the statement, up to the line that opens the proof.
        j = i
        opened = False
        while j < len(lines):
            stmt = lines[j]
            if j > i and stmt and not stmt[0].isspace():
                break  # ran into the next declaration: not a tactic proof
            if stmt.rstrip().endswith(":= by"):
                out.append(stmt)
                opened = True
                j += 1
                break
            if ":= by " in stmt:
                out.append(stmt[: stmt.index(":= by ")] + ":= by")
                opened = True
                j += 1
                break
            if re.search(r":=\s*\S", stmt) or stmt.rstrip().endswith("where"):
                break  # a term proof or a structure: leave it alone
            out.append(stmt)
            j += 1

        if not opened:
            # Leave the declaration untouched.
            del out[len(out) - (j - i):]
            while i < len(lines):
                out.append(lines[i])
                i += 1
                if i < len(lines) and lines[i] and not lines[i][0].isspace():
                    break
            continue

        # Skip the proof: every following line that is indented or blank.
        # Comments at the top level of the proof are kept as an outline.
        outline = []
        while j < len(lines) and (not lines[j] or lines[j][0].isspace()):
            if lines[j].startswith("  -- "):
                outline.append(lines[j])
            j += 1
        if outline:
            out.append("  -- Outline of one proof:")
            out.extend(outline)
        out.append("  sorry")
        out.append("")
        count += 1
        i = j
    return "\n".join(out), count


def generate() -> dict[pathlib.Path, str]:
    files = {}
    for name, only in EXERCISES.items():
        source = SOURCE / name
        rel = source.relative_to(SOURCE)
        module = "Exercises." + ".".join(rel.with_suffix("").parts)
        body, count = blank_proofs(source.read_text(), only)
        if count != (len(only) if only is not None else count) or count == 0:
            raise SystemExit(f"{name}: expected to blank {only}, blanked {count}")
        header = HEADER.format(source=source.relative_to(ROOT), module=module,
                               given="" if only is None else GIVEN)
        files[TARGET / rel] = header + body
    return files


def main() -> int:
    files = generate()
    if "--check" in sys.argv:
        stale = [p for p, text in files.items() if not p.exists() or p.read_text() != text]
        extra = [p for p in TARGET.rglob("*.lean") if p not in files] if TARGET.exists() else []
        for p in stale + extra:
            print(f"out of date: {p.relative_to(ROOT)}")
        return 1 if stale or extra else 0
    for old in TARGET.rglob("*.lean") if TARGET.exists() else []:
        if old not in files:
            old.unlink()
    for path, text in files.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    print(f"wrote {len(files)} exercise files to {TARGET.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
