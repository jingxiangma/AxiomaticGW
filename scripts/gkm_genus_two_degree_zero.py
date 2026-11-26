#!/usr/bin/env python3
"""Replay three native genus-two degree-zero descendant claims in Lean.

This diagnostic preserves exact equivariant values and producer provenance.
The ordinary values use the proved degree-zero descendant--ancestor comparison
and existing finite-seed ancestor algorithm. Localization geometry, symbolic
specialization and class-valued CohFT import remain separate obligations.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
import check_gkm_inputs as codec
from export_gkm_inputs import producer_source
from export_admcycles_certificate import rational, rational_text, vector
from gkm_three_point_descendants import TARGETS, explore as native_explore, read_report as parse_report

KIND = "gkm_localization.genus_two_degree_zero_comparison"
REQUESTS = {
    "X0": [((0,), (2,), ("unit",))],
    "X1": [((0, 0), (2,), ("unit",))],
    "X2": [((0, 0, 0), (2,), ("unit",))],
}
# Computed by SurfaceGenusTwo.onePointAncestorValue, not supplied as seeds.
EXPECTED = {"X0": Fraction(7, 640), "X1": Fraction(7, 720), "X2": Fraction(49, 5760)}


def read_report(raw):
    """Validate requests and provenance without accepting the supplied answers."""
    return parse_report(raw, requests=REQUESTS, genus=2, kind=KIND)


def check_report(raw):
    report, grouped = read_report(raw)
    for target, cases in grouped.items():
        codec.require(codec.rational(cases[0]["ordinary"]) == EXPECTED[target],
                      "Native value differs from the held ancestor constant")
    return report


def query_text(case):
    labels = {"unit": ".unit", "H": ".hyperplane", "E1": ".exceptional 0",
              "E2": ".exceptional 1", "pt": ".point"}
    insertions = ", ".join("⟨" + labels[a] + ", " + str(p) + "⟩"
                           for p, a in zip(case["powers"], case["labels"]))
    return ("⟨" + str(case["genus"]) + ", " + vector(list(map(str, case["class"]))) +
            ", [" + insertions + "]⟩")


def emit(raw, *, cached=False):
    """Bind each complete incoming query and value to the original evaluator."""
    _, grouped = read_report(raw)
    name = "GenusTwoDegreeZeroBinding" if cached else "GenusTwoDegreeZeroReplay"
    imported = ("AxiomaticGW.GKM.Fixtures.GenusTwoDegreeZeroReplay" if cached else
                "AxiomaticGW.Surfaces.GenusTwoDegreeZeroDescendants")
    lines = ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
             "Released under Apache 2.0 license as described in the file LICENSE.",
             "Authors: JMA", "-/", "module", "", "public import " + imported, "",
             "/-!", "# Genus-two degree-zero descendant replay on all three targets", "",
             "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
             "The full incoming ordinary claims are checked against the reconstructed values.",
             "Geometric interpretation uses the named inputs of the soundness theorem.",
             "This does not certify localization or import CohFT classes.", "-/", "",
             "@[expose] public section", "", "set_option Elab.async false", "",
             "namespace AxiomaticGW.GKM." + name, ""]
    for target, namespace, surface in TARGETS:
        cases = grouped[target]
        lines += [f"namespace {namespace}", "",
                  "/-- Complete incoming requests, preserving the target and full class. -/",
                  f"def requests : Fin {len(cases)} → SurfaceQuery .{surface} :=",
                  "  " + vector([query_text(c) for c in cases]), "",
                  "/-- Exact ordinary values supplied by the pinned producer. -/",
                  f"def values : Fin {len(cases)} → ℚ :=",
                  "  " + vector([rational_text(rational(c["ordinary"])) for c in cases]), "",
                  "/-- Every supplied answer belongs to the complete requested descendant. -/",
                  "theorem accepted : ∀ i,",
                  "    SurfaceGenusTwo.degreeZeroOnePointQueryValue? (requests i) =",
                  "      some (values i) := by"]
        if cached:
            fixture = "GenusTwoDegreeZeroReplay." + namespace
            lines += [f"  have hq : requests = {fixture}.requests := by decide +kernel",
                      f"  have hv : values = {fixture}.values := by decide +kernel",
                      "  rw [hq, hv]", f"  exact {fixture}.accepted"]
        else:
            lines += ["  decide +kernel"]
        lines += ["", f"end {namespace}", ""]
    return "\n".join(lines + ["end AxiomaticGW.GKM." + name, ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    native = commands.add_parser("explore")
    native.add_argument("--producer", required=True, type=Path)
    native.add_argument("--output", required=True, type=Path)
    check = commands.add_parser("check")
    check.add_argument("report", type=Path)
    replay = commands.add_parser("replay")
    replay.add_argument("report", type=Path)
    replay.add_argument("--output", required=True, type=Path)
    replay.add_argument("--check", action="store_true")
    replay.add_argument("--cached", action="store_true")
    args = parser.parse_args()
    if args.command == "explore":
        producer, pin = producer_source(args.producer)
        with tempfile.TemporaryDirectory(prefix="gw-genus-two-zero-") as directory:
            os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
            for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
                cache = Path(directory) / name
                cache.mkdir()
                os.environ[name] = str(cache)
            (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
            report = native_explore(producer, pin, requests=REQUESTS, genus=2, kind=KIND)
        raw = json.dumps(report, sort_keys=True, indent=2) + "\n"
        check_report(raw)
        args.output.write_text(raw)
    elif args.command == "check":
        check_report(args.report.read_bytes())
    else:
        result = emit(args.report.read_bytes(), cached=args.cached)
        if args.check:
            codec.require(args.output.read_text() == result,
                          "Saved replay differs from generated source")
        else:
            args.output.write_text(result)
    print("Genus-two degree-zero report processed; Lean replay is the acceptance step.")


if __name__ == "__main__":
    main()
