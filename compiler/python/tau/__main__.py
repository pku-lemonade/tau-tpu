"""The command line of the frontend.

    python3 -m tau kernel.py -o out
        Trace the program and write out/kernel.mlir, the input of `tauc`,
        and out/traced.json, the same program as a source file.

    python3 -m tau kernel.py --run buffers.json
        Run the program on real numbers and print the final buffers, in the
        format `tau-sim` prints.

    python3 -m tau kernel.py --timeline buffers.json
        Run it and print the events of its pinned operations, in the format
        `tau-sim --timeline` prints.

The program is the kernel that the file binds to the name `kernel`, or to the
name given with --entry.
"""

import argparse
import json
import pathlib
import runpy
import sys

import tau


def main():
    parser = argparse.ArgumentParser(prog="python3 -m tau")
    parser.add_argument("file", help="a Python file that defines a kernel")
    parser.add_argument("-o", dest="out", help="directory to write to")
    parser.add_argument("--entry", default="kernel",
                        help="the name the file gives its program")
    parser.add_argument("--run", metavar="BUFFERS")
    parser.add_argument("--timeline", metavar="BUFFERS")
    args = parser.parse_args()

    try:
        scope = runpy.run_path(args.file)
        target = scope.get(args.entry)
        if not isinstance(target, tau.Kernel):
            sys.exit(f"{args.file}: no kernel named '{args.entry}'")

        if args.out:
            program = tau.trace(target)
            out = pathlib.Path(args.out)
            out.mkdir(parents=True, exist_ok=True)
            (out / "kernel.mlir").write_text(program.mlir())
            (out / "traced.json").write_text(
                json.dumps(program.source(), indent=2) + "\n")

        for path, timeline in ((args.run, False), (args.timeline, True)):
            if not path:
                continue
            given = json.loads(pathlib.Path(path).read_text())
            buffers, events = tau.run(target, given["buffers"], given["lanes"])
            if timeline:
                print(json.dumps(events, indent=2))
            else:
                print(json.dumps({"lanes": given["lanes"], "buffers": buffers},
                                 indent=2))
    except tau.TauError as error:
        sys.exit(f"{args.file}: {error}")


if __name__ == "__main__":
    main()
