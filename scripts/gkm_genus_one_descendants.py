#!/usr/bin/env python3
"""Native all-arity genus-one localization and claim-bound Lean replay.

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

KIND = "gkm_localization.genus_one_descendants"
REQUESTS = {
    "X0": [((0,), (1,), ("unit",)),
           ((0,), (2,0), ("unit","unit")),
           ((0,), (1,1), ("unit","unit")),
           ((0,), (1,1,1), ("unit","unit","unit")),
           ((0,), (1,0), ("unit","H")),
           ((0,), (0,1), ("H","unit")),
           ((0,), (1,1,1,1), ("unit","unit","unit","unit")),
           ((1,), (2,), ("pt",)),
           ((1,), (3,), ("H",)),
           ((1,), (4,), ("unit",)),
           ((1,), (3,0), ("pt","unit")),
           ((1,), (3,0), ("H","H")),
           ((1,), (), ()),
           ((2,), (5,), ("pt",))],
    "X1": [((0,0), (1,), ("unit",)),
           ((0,0), (2,0), ("unit","unit")),
           ((0,0), (1,1,1), ("unit","unit","unit")),
           ((0,0), (1,0), ("unit","E1")),
           ((0,0), (0,1), ("E1","unit")),
           ((1,0), (1,), ("E1",)),
           ((1,0), (2,), ("unit",)),
           ((1,0), (1,0), ("E1","E1")),
           ((1,0), (), ()),
           ((2,0), (2,), ("E1",)),
           ((0,1), (1,), ("pt",)),
           ((1,1), (3,), ("H",))],
    "X2": [((0,0,0), (1,), ("unit",)),
           ((0,0,0), (1,1,1), ("unit","unit","unit")),
           ((0,0,0), (1,0), ("unit","E2")),
           ((1,0,0), (1,), ("E1",)),
           ((0,1,0), (1,), ("E1",)),
           ((0,1,0), (1,), ("E2",)),
           ((1,0,0), (2,), ("unit",)),
           ((0,1,0), (1,0), ("E2","E2")),
           ((0,0,1), (1,), ("H",)),
           ((0,0,1), (1,), ("E1",)),
           ((0,0,1), (), ()),
           ((1,0,0), (), ()),
           ((2,0,0), (2,), ("E1",)),
           ((1,0,1), (1,), ("pt",)),
           ((1,1,1), (3,), ("H",))],
}


def read_report(raw):
    return parse_report(raw, requests=REQUESTS, kind=KIND, genus=1)


def query_text(case):
    label = {"unit": ".unit", "H": ".hyperplane", "E1": ".exceptional 0",
             "E2": ".exceptional 1", "pt": ".point"}
    insertions = ", ".join("⟨" + label[a] + ", " + str(p) + "⟩"
                           for p, a in zip(case["powers"], case["labels"]))
    return "⟨1, " + vector(list(map(str, case["class"]))) + ", [" + insertions + "]⟩"


def emit(raw):
    _, grouped = read_report(raw)
    lines = ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
             "Released under Apache 2.0 license as described in the file LICENSE.",
             "Authors: JMA", "-/", "module", "",
             "public import AxiomaticGW.Surfaces.Fixtures.GenusOneDescendants", "",
             "/-!", "# Native genus-one descendant replay at multiple arities", "",
             "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
             "Actual incoming claims are checked against the proved all-arity evaluator.",
             "The digest records provenance; geometric applicability remains conditional.", "-/", "",
             "@[expose] public section", "",
             "namespace AxiomaticGW.GKM.GenusOneDescendantReplay", ""]
    for target, namespace, surface in TARGETS:
        cases = grouped[target]
        lines += [f"namespace {namespace}", "",
                  "/-- Actual incoming full requests in source order. -/",
                  f"def requests : Fin {len(cases)} → SurfaceQuery .{surface} :=",
                  "  ![" + ",\n    ".join(map(query_text, cases)) + "]", "",
                  "/-- Actual incoming ordinary values, without recomputation by the exporter. -/",
                  f"def values : Fin {len(cases)} → ℚ :=",
                  "  ![" + ",\n    ".join(rational_text(rational(c["ordinary"])) for c in cases) + "]", "",
                  "/-- Full request coverage is fixed separately from incoming values. -/",
                  "theorem coverage : Finset.univ.image requests =",
                  f"    (SurfaceGenusOneDescendants.requests .{surface}).toFinset := by decide +kernel", "",
                  "/-- Genus, full class, arity, insertion powers and labels are claim-bound. -/",
                  "theorem accepted : ∀ i, SurfaceGenusOne.queryValue? (requests i) =",
                  "    some (values i) := by decide +kernel", "",
                  f"end {namespace}", ""]
    return "\n".join(lines + ["end AxiomaticGW.GKM.GenusOneDescendantReplay", ""])


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
        with tempfile.TemporaryDirectory(prefix="gw-genus-one-native-") as directory:
            os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
            for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
                cache = Path(directory) / name
                cache.mkdir()
                os.environ[name] = str(cache)
            (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
            report = native_explore(producer, pin, requests=REQUESTS, kind=KIND, genus=1)
        args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    else:
        result = emit(args.report.read_bytes())
        if args.check:
            codec.require(args.output.read_text() == result, "Saved replay differs from generated source")
        else:
            args.output.write_text(result)


if __name__ == "__main__":
    main()
