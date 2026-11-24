#!/usr/bin/env python3
"""Generate the course exercises from the finished proofs.

Every file under Tau/Proofs/ becomes a file under course/Exercises/ in which
each tactic proof is replaced by `sorry`. Statements, doc comments and imports
are kept, so an exercise file is the finished file with the proofs taken out.
The finished file is the solution.

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
Build this file alone with:

    lake build {module}
-/

"""

DECL = re.compile(r"^(theorem|lemma)\b")


def blank_proofs(text: str) -> tuple[str, int]:
    """Replace the body of every `theorem ... := by` with `sorry`."""
    lines = text.split("\n")
    out: list[str] = []
    count = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        if not DECL.match(line):
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
    for source in sorted(SOURCE.rglob("*.lean")):
        rel = source.relative_to(SOURCE)
        module = "Exercises." + ".".join(rel.with_suffix("").parts)
        body, count = blank_proofs(source.read_text())
        if count == 0:
            continue
        header = HEADER.format(source=source.relative_to(ROOT), module=module)
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
    for path, text in files.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    print(f"wrote {len(files)} exercise files to {TARGET.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
