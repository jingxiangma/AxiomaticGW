#!/usr/bin/env python3
"""Explore and replay the exact genus-two F1 fiber hyperplane descendant.

The incoming ordinary value is checked against the separately proved full
query. Exact equivariant specialization remains Python preflight; this does
not certify localization geometry or import a class-valued CohFT.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
from export_gkm_inputs import producer_source
from gkm_three_point_descendants import explore as native_explore, read_report as parse_report
from export_admcycles_certificate import rational_text
import check_gkm_inputs as codec

KIND = "gkm_localization.f1_fiber_h"
REQUESTS = {"X0": [], "X1": [((0, 1), (1, 0, 0), ("H", "pt", "pt"))], "X2": []}


def read_report(raw):
    """Check the exact request and provenance without accepting its ordinary answer."""
    return parse_report(raw, requests=REQUESTS, genus=2, kind=KIND)


def emit(raw):
    _, grouped = read_report(raw)
    case = grouped["X1"][0]
    labels = {"H": ".hyperplane", "pt": ".point"}
    insertions = ", ".join(f"⟨{labels[a]}, {p}⟩" for p, a in zip(case["powers"], case["labels"]))
    curve = ", ".join(map(str, case["class"]))
    query = f"⟨{case['genus']}, ![{curve}], [{insertions}]⟩"
    value = rational_text(codec.rational(case["ordinary"]))
    return "\n".join([
        "/-", "Copyright (c) 2026 JMA. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        "Authors: JMA", "-/", "module", "",
        "public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHValue", "",
        "/-!", "# Incoming genus-two F1 fiber hyperplane descendant", "",
        "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
        "The incoming ordinary value is bound to the complete held descendant query.",
        "Geometric interpretation retains the original equation and seed hypotheses.",
        "This does not certify equivariant localization or import CohFT classes.",
        "-/", "", "@[expose] public section", "",
        "namespace AxiomaticGW.GKM.BlowupF1FiberHReplay", "",
        "open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder", "",
        "/-- Incoming class, genus, ordered states and powers, including both point markings. -/",
        "def request : SurfaceQuery .hirzebruchOne :=", "  " + query, "",
        "/-- The actual incoming ordinary rational, independently checked by `accepted`. -/",
        "def value : ℚ := " + value, "",
        "/-- Exact binding to the separately held full fiber descendant request. -/",
        "theorem request_eq : request = BlowupF1FiberHValue.query := by", "  decide +kernel", "",
        "/-- The incoming value agrees with the proved reconstruction at that exact query. -/",
        "theorem accepted :",
        "    canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0) (.inr request) = value := by",
        "  rw [request_eq, BlowupF1FiberHValue.reconstructed_query]",
        "  norm_num only [value]", "",
        "end AxiomaticGW.GKM.BlowupF1FiberHReplay", ""])


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
        with tempfile.TemporaryDirectory(prefix="gw-f1-fiber-h-") as directory:
            os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
            for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
                cache = Path(directory) / name
                cache.mkdir()
                os.environ[name] = str(cache)
            (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
            report = native_explore(producer, pin, requests=REQUESTS, genus=2, kind=KIND)
        raw = (json.dumps(report, sort_keys=True, indent=2) + "\n").encode()
        read_report(raw)
        args.output.write_bytes(raw)
    else:
        source = emit(args.report.read_bytes())
        if args.check:
            codec.require(args.output.read_text() == source, "Replay source differs")
        else:
            args.output.write_text(source)


if __name__ == "__main__":
    main()
