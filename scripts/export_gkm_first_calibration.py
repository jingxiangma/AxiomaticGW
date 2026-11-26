#!/usr/bin/env python3
"""Replay actual incoming ordinary calibration matrices against held Lean values.

Python checks equivariant matrix multiplication and regular specialization
with independent exact polynomial arithmetic. Lean checks the incoming
ordinary entries, full classes, labels, powers and complete finite coverage.
Neither stage proves the geometric localization formula or CohFT axioms.
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path

import check_gkm_inputs as codec
from export_admcycles_certificate import rational_matrix, vector

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "environments/gkm-inputs-osx-arm64.json"
TARGETS = [("X0", "Plane", "plane"), ("X1", "OneBlowup", "hirzebruchOne"),
           ("X2", "TwoBlowups", "blowupTwo")]


def read_report(raw):
    report = json.loads(raw, object_pairs_hook=codec.unique_object)
    source = json.loads(INPUT.read_text())
    codec.require(report["schema_version"] == 1 and type(report["schema_version"]) is int and
                  report["kind"] == "gkm_localization.first_calibration_comparison", "Wrong schema")
    codec.require(report["input_sha256"] == hashlib.sha256(INPUT.read_bytes()).hexdigest() and
                  report["source"] == source["source"], "Changed source provenance")
    codec.require(report["environment"] == {"sage": "10.9", "admcycles": "1.4"}, "Wrong environment")
    codec.require(report["primary_deformation"] == "zero" and
                  report["coefficient_convention"] ==
                  "S = eta^-1 times the node/retained-input correlator matrix", "Wrong convention")
    grouped = {target: [] for target, _, _ in TARGETS}
    frames = {f["target"]: f for f in source["targets"]}
    for case in report["cases"]:
        codec.require(case["target"] in grouped, "Unknown target")
        frame = frames[case["target"]]
        codec.require(case["basis"] == frame["basis"], "Changed basis order")
        beta = tuple(map(codec.integer, case["class"]))
        weights = frame["energy_weights"]
        codec.require(len(beta) == len(weights) and all(x >= 0 for x in beta), "Invalid full class")
        energy = sum(x * w for x, w in zip(beta, weights))
        codec.require(0 < energy <= 3 and codec.integer(case["energy"]) == energy, "Wrong energy")
        codec.require(codec.integer(case["inverse_loop_power"]) == 1 and
                      codec.integer(case["tail_psi_power"]) == 0, "Wrong cotangent index")
        rank = len(frame["basis"])
        inverse = codec.matrix(frame["inverse_metric"], rank)

        def decoded_matrix(key):
            data = case[key]
            codec.require(isinstance(data, list) and len(data) == rank and
                          all(isinstance(row, list) and len(row) == rank for row in data),
                          "Wrong matrix shape")
            decoded = []
            for row in data:
                converted = []
                for value in row:
                    codec.require(set(value) == {"numerator", "denominator"}, "Wrong function fields")
                    converted.append(codec.RationalFunction(codec.polynomial(value["numerator"]),
                                                             codec.polynomial(value["denominator"])))
                decoded.append(converted)
            return decoded

        paired, raised = decoded_matrix("paired_equivariant"), decoded_matrix("operator_equivariant")
        ordinary = case["operator_ordinary"]
        rational_matrix(ordinary, rank, rank)
        for i in range(rank):
            for j in range(rank):
                codec.require(sum(inverse[i][k] * paired[k][j] for k in range(rank)) == raised[i][j],
                              "Incorrect inverse-metric contraction")
                codec.require(raised[i][j].ordinary() == codec.rational(ordinary[i][j]),
                              "Incorrect ordinary specialization")
        grouped[case["target"]].append(case)
    for target, cases in grouped.items():
        weights = frames[target]["energy_weights"]
        expected = {b for b in itertools.product(*(range(3 // w + 1) for w in weights))
                    if 0 < sum(x * w for x, w in zip(b, weights)) <= 3}
        received = [tuple(c["class"]) for c in cases]
        codec.require(len(received) == len(set(received)) and set(received) == expected,
                      "Incomplete or duplicate curve coverage")
    return report, grouped


def emit(raw):
    _, grouped = read_report(raw)
    lines = ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
             "Released under Apache 2.0 license as described in the file LICENSE.",
             "Authors: JMA", "-/", "module", "",
             "public import AxiomaticGW.Surfaces.Fixtures.FirstCalibration", "",
             "/-!", "# Incoming GKM first-calibration matrix replay", "",
             "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
             "The digest is provenance only. Kernel checks bind ordinary entries to the",
             "held surface values, full classes and fixed inverse-loop/psi indexing.",
             "Equivariant specialization is checked separately by exact Python arithmetic.",
             "No localization theorem, CohFT class or symplecticity is asserted.", "-/", "",
             "@[expose] public section", "", "namespace AxiomaticGW.GKM.FirstCalibrationReplay", ""]
    label = {"unit": ".unit", "H": ".hyperplane", "E1": ".exceptional 0",
             "E2": ".exceptional 1", "pt": ".point"}
    stacked = lambda xs: "![" + ",\n    ".join(xs) + "]"
    for target, namespace, surface in TARGETS:
        cases = grouped[target]
        n, rank = len(cases), len(cases[0]["basis"])
        lines += [f"namespace {namespace}", "", "/-- Actual incoming full curve coordinates. -/",
                  f"def classes : Fin {n} → SurfaceTarget.Curve .{surface} :=",
                  "  " + stacked([vector(list(map(str, c["class"]))) for c in cases]), "",
                  "/-- The actual incoming order of homogeneous basis labels. -/",
                  f"def labels : Fin {rank} → SurfaceBasisLabel .{surface} :=",
                  "  " + vector([label[x] for x in cases[0]["basis"]]), "",
                  "/-- Imported ordinary operator entries, with rows as output coordinates. -/",
                  f"def entries : Fin {n} → Matrix (Fin {rank}) (Fin {rank}) ℚ :=",
                  "  " + stacked([rational_matrix(c["operator_ordinary"], rank, rank) for c in cases]), "",
                  "/-- Imported inverse-loop powers. -/", f"def powers : Fin {n} → ℕ :=",
                  "  " + vector([str(c["inverse_loop_power"]) for c in cases]), "",
                  "/-- Imported powers at the retained tail marking. -/", f"def psiPowers : Fin {n} → ℕ :=",
                  "  " + vector([str(c["tail_psi_power"]) for c in cases]), "",
                  "/-- Every basis state appears exactly once. -/",
                  "theorem labels_bijective : Function.Bijective labels := by decide +kernel", "",
                  "/-- Every positive class of energy at most three is present. -/",
                  "theorem coverage : Finset.univ.image classes =",
                  f"    (SurfaceTarget.bounded .{surface} 3).erase 0 := by decide +kernel", "",
                  "/-- The incoming cotangent powers are precisely the first calibration coefficient. -/",
                  "theorem indices : ∀ i, powers i = 1 ∧ psiPowers i = 0 := by decide +kernel", "",
                  "/-- Every incoming entry agrees with the independently held sparse claim. -/",
                  "theorem accepted : ∀ i row col, entries i row col =",
                  f"    SurfaceFirstCalibration.values .{surface} (classes i) (labels row) (labels col) := by",
                  "  decide +kernel", "",
                  "/-- Accepted incoming entries equal the proved primary reconstruction. -/",
                  "theorem reconstructed (i row col) : entries i row col =",
                  f"    SurfaceDescendant.firstCalibrationMatrix .{surface} (classes i)",
                  "      (labels row) (labels col) := by",
                  "  rw [accepted, SurfaceFirstCalibration.values_eq]", "",
                  f"end {namespace}", ""]
    lines += ["end AxiomaticGW.GKM.FirstCalibrationReplay", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = emit(args.report.read_bytes())
    if args.check:
        codec.require(args.output.read_text() == result, "Saved replay differs from generated source")
    else:
        args.output.write_text(result)


if __name__ == "__main__":
    main()
