"""Shared native exploration and offline Lean-source replay for exact GKM reports."""
import argparse
import json
import operator
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from export_gkm_inputs import producer_source


def explore_report(producer_path, requests, genus, kind):
    """Run each report in its own Sage process, including repeated calls from one notebook."""
    with tempfile.TemporaryDirectory(prefix="gw-gkm-report-") as directory:
        root = Path(directory)
        environment = os.environ.copy()
        for var in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            cache = root / var
            cache.mkdir()
            environment[var] = str(cache)
        (root / "DOT_SAGE" / "admcycles").mkdir()
        request = root / "requests.json"
        request.write_text(json.dumps({"requests": requests, "genus": genus, "kind": kind},
                                      default=operator.index))
        output = root / "report.json"
        subprocess.run([sys.executable, "-B", __file__, str(producer_path), str(request), str(output)],
                       env=environment, check=True)
        return output.read_bytes()


def report_cli(description, *, requests, genus, kind, emit, argv=None):
    """Validate the generated report with its exact request frame before writing it."""
    parser = argparse.ArgumentParser(description=description)
    commands = parser.add_subparsers(dest="command", required=True)
    native = commands.add_parser("explore")
    native.add_argument("--producer", type=Path, required=True)
    native.add_argument("--output", type=Path, required=True)
    replay = commands.add_parser("replay")
    replay.add_argument("report", type=Path)
    replay.add_argument("--output", type=Path, required=True)
    replay.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    if args.command == "explore":
        raw = explore_report(args.producer, requests, genus, kind)
        emit(raw)
        args.output.write_bytes(raw)
    else:
        source = emit(args.report.read_bytes())
        if args.check:
            if args.output.read_text() != source:
                parser.exit(1, "Saved claims differ from regenerated source\n")
        else:
            args.output.write_text(source)


if __name__ == "__main__":
    from gkm_three_point_descendants import explore

    parser = argparse.ArgumentParser(description="Compute one GKM report in an isolated Sage process.")
    parser.add_argument("producer", type=Path)
    parser.add_argument("request", type=Path)
    parser.add_argument("output", type=Path)
    options = parser.parse_args()
    producer, pin = producer_source(options.producer)
    report = explore(producer, pin, **json.loads(options.request.read_text()))
    options.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
