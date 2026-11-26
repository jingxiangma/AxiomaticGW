#!/usr/bin/env python3
"""Native all-arity genus-zero localization and claim-bound Lean replay.

The held requests include stable descendants and positive-degree unstable
arities on all three fixed surfaces. The common exploration transport only
calls the producer; it contains no copy of the Lean reconstruction algorithm.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
import check_gkm_inputs as codec
from export_admcycles_certificate import rational, rational_text, vector
from export_gkm_inputs import producer_source
from gkm_three_point_descendants import TARGETS, explore as native_explore, read_report as parse_report

KIND = "gkm_localization.genus_zero_descendants"
REQUESTS = {
    "X0": [((0,), (1,0,0,0), ("unit","unit","unit","pt")),
           ((0,), (1,1,0,0,0), ("unit","unit","unit","unit","pt")),
           ((0,), (1,1,1,0,0,0), ("unit","unit","unit","unit","unit","pt")),
           ((0,), (2,0,0,0,0), ("unit","unit","unit","unit","pt")),
           ((1,), (3,0,0,0), ("pt","unit","unit","H")),
           ((1,), (4,0,0,0), ("H","H","unit","unit")),
           ((1,), (1,0,0,0), ("pt","H","H","H")),
           ((1,), (4,0,0,0,0), ("pt","unit","unit","unit","H")),
           ((1,), (1,), ("pt",)),
           ((1,), (2,), ("H",)),
           ((1,), (2,0), ("pt","unit")),
           ((1,), (2,0), ("H","H"))],
    "X1": [((0,0), (1,0,0,0), ("unit","E1","E1","unit")),
           ((0,0), (1,1,0,0,0), ("unit","unit","E1","E1","unit")),
           ((1,0), (2,0,0,0), ("E1","E1","unit","unit")),
           ((2,0), (2,1,0,0), ("E1","E1","unit","unit")),
           ((1,0), (), ()),
           ((1,0), (0,), ("E1",)),
           ((1,0), (1,), ("unit",)),
           ((1,0), (0,0), ("E1","E1")),
           ((0,1), (0,), ("pt",)),
           ((1,1), (3,0,0,0), ("pt","unit","unit","H"))],
    "X2": [((0,0,0), (1,0,0,0), ("unit","E1","E2","unit")),
           ((0,0,0), (1,1,0,0,0), ("unit","unit","E2","E2","unit")),
           ((1,0,0), (2,0,0,0), ("E1","E1","unit","unit")),
           ((0,1,0), (2,0,0,0), ("E1","E1","unit","unit")),
           ((0,1,0), (2,0,0,0), ("E2","E2","unit","unit")),
           ((0,0,1), (0,0,0,1), ("H","E1","E2","unit")),
           ((0,0,1), (), ()),
           ((1,0,0), (), ()),
           ((0,1,0), (), ()),
           ((1,0,0), (1,), ("unit",)),
           ((0,1,1), (0,), ("pt",)),
           ((1,0,1), (0,), ("pt",))],
}


def read_report(raw):
    return parse_report(raw, requests=REQUESTS, kind=KIND)


def query_text(case):
    label = {"unit": ".unit", "H": ".hyperplane", "E1": ".exceptional 0",
             "E2": ".exceptional 1", "pt": ".point"}
    insertions = ", ".join("⟨" + label[a] + ", " + str(p) + "⟩"
                           for p, a in zip(case["powers"], case["labels"]))
    return "⟨0, " + vector(list(map(str, case["class"]))) + ", [" + insertions + "]⟩"


def emit(raw):
    _, grouped = read_report(raw)
    lines = ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
             "Released under Apache 2.0 license as described in the file LICENSE.",
             "Authors: JMA", "-/", "module", "",
             "public import AxiomaticGW.Surfaces.Fixtures.GenusZeroDescendants", "",
             "/-!", "# Native genus-zero descendant replay at multiple arities", "",
             "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
             "Actual incoming claims are checked against the proved all-arity evaluator.",
             "The digest records provenance; geometric applicability remains conditional.", "-/", "",
             "@[expose] public section", "",
             "namespace AxiomaticGW.GKM.GenusZeroDescendantReplay", ""]
    for target, namespace, surface in TARGETS:
        cases = grouped[target]
        lines += [f"namespace {namespace}", "",
                  f"def requests : Fin {len(cases)} → SurfaceQuery .{surface} :=",
                  "  ![" + ",\n    ".join(map(query_text, cases)) + "]", "",
                  f"def values : Fin {len(cases)} → ℚ :=",
                  "  " + vector([rational_text(rational(c["ordinary"])) for c in cases]), "",
                  "/-- Full request coverage is fixed separately from incoming values. -/",
                  "theorem coverage : Finset.univ.image requests =",
                  f"    (SurfaceGenusZeroDescendants.requests .{surface}).toFinset := by decide +kernel", "",
                  "/-- Genus, full class, arity, insertion powers and labels are claim-bound. -/",
                  "theorem accepted : ∀ i, SurfaceGenusZero.queryValue? (requests i) =",
                  "    some (values i) := by decide +kernel", "",
                  f"end {namespace}", ""]
    return "\n".join(lines + ["end AxiomaticGW.GKM.GenusZeroDescendantReplay", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    native = commands.add_parser("explore")
    native.add_argument("--producer", required=True, type=Path)
    native.add_argument("--output", required=True, type=Path)
    replay = commands.add_parser("replay")
    replay.add_argument("report", type=Path)
    replay.add_argument("--output", required=True, type=Path)
    replay.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.command == "explore":
        producer, pin = producer_source(args.producer)
        with tempfile.TemporaryDirectory(prefix="gw-genus-zero-native-") as directory:
            os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
            for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
                cache = Path(directory) / name
                cache.mkdir()
                os.environ[name] = str(cache)
            (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
            report = native_explore(producer, pin, requests=REQUESTS, kind=KIND)
        args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    else:
        result = emit(args.report.read_bytes())
        if args.check:
            codec.require(args.output.read_text() == result, "Saved replay differs from generated source")
        else:
            args.output.write_text(result)


if __name__ == "__main__":
    main()
