#!/usr/bin/env python3
"""Explore and replay the three held genus-two plane line queries.

Lean checks incoming ordinary values against the proved BP reconstruction.
Exact equivariant specialization is separately checked in Python; this does
not certify the producer's localization theorem or import CohFT classes.
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

KIND = "gkm_localization.plane_genus_two_line"
REQUESTS = {
    "X0": [((1,), (0, 0, 0, 0), ("pt", "pt", "pt", "pt")),
           ((1,), (1, 0, 0, 0), ("H", "pt", "pt", "pt")),
           ((1,), (1, 0, 0), ("pt", "pt", "pt"))],
    "X1": [],
    "X2": [],
}


def read_report(raw):
    return parse_report(raw, requests=REQUESTS, genus=2, kind=KIND)


def emit(raw):
    _, grouped = read_report(raw)
    indexed = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
               for c in grouped["X0"]}
    cases = [indexed[q] for q in REQUESTS["X0"]]
    label = {"pt": ".point", "H": ".hyperplane"}
    queries = []
    for c in cases:
        states = ", ".join(f"⟨{label[a]}, {p}⟩" for p, a in zip(c["powers"], c["labels"]))
        queries.append(f"⟨{c['genus']}, ![{c['class'][0]}], [{states}]⟩")
    values = ", ".join(rational_text(codec.rational(c["ordinary"])) for c in cases)
    return "\n".join([
        "/-", "Copyright (c) 2026 JMA. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        "Authors: JMA", "-/", "module", "",
        "public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine", "",
        "/-!", "# Native genus-two plane line replay", "",
        "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
        "Incoming ordinary values are checked against the full held queries.",
        "This certificate does not prove equivariant localization or CohFT applicability.",
        "-/", "", "@[expose] public section", "",
        "namespace AxiomaticGW.GKM.PlaneGenusTwoLineReplay", "",
        "open BelorousskiPandharipande", "",
        "/-- The three incoming full line queries, in N/H/P order. -/",
        "def requests : Fin 3 → SurfaceQuery .plane :=",
        "  ![" + ",\n    ".join(queries) + "]", "",
        "/-- Incoming ordinary rational values, bound to the requests by `accepted`. -/",
        "def values : Fin 3 → ℚ := ![" + values + "]", "",
        "/-- Exact full-class, genus and ordered insertion coverage. -/",
        "theorem coverage : ∀ i, requests i = planeCanonicalQueries 1 i := by",
        "  decide +kernel", "",
        "/-- Each incoming value is bound to its actual requested invariant. -/",
        "theorem accepted : ∀ i, planeCheckCanonicalClaim 1 GenusTwoPlaneLine.values",
        "    (requests i) (values i) = true := by",
        "  intro i",
        "  rw [planeCheckCanonicalClaim, GenusTwoPlaneLine.accepted, Bool.and_true]",
        "  fin_cases i <;> decide +kernel", "",
        "end AxiomaticGW.GKM.PlaneGenusTwoLineReplay", ""])


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
        with tempfile.TemporaryDirectory(prefix="gw-plane-genus-two-") as directory:
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
