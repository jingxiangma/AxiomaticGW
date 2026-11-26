#!/usr/bin/env python3
"""Explore and replay the thirty held higher-calibration requests.

Native localization and exact ordinary specialization are independent of the
Lean matrix recursion. The exporter replays actual incoming entries, powers,
classes and labels. It does not certify equivariant geometry or CohFT classes.
"""

import argparse
import functools
from fractions import Fraction
import hashlib
import importlib.metadata
import itertools
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
import check_gkm_inputs as codec
from export_admcycles_certificate import rational_matrix, vector
from export_gkm_inputs import producer_source, target_specifications
from explore_gkm_first_calibration import expected_matrix

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "environments/gkm-inputs-osx-arm64.json"
TARGETS = [("X0", "Plane", "plane"), ("X1", "OneBlowup", "hirzebruchOne"),
           ("X2", "TwoBlowups", "blowupTwo")]
REQUESTS = {
    "X0": [(p, (1,)) for p in range(2, 7)] + [(4, (2,))],
    "X1": [(p, b) for b in [(1, 0), (0, 1), (1, 1), (2, 0)] for p in (2, 3)],
    "X2": [(p, b) for b in [(1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 1),
                            (1, 0, 1), (1, 1, 1), (2, 0, 0), (0, 2, 0)] for p in (2, 3)],
}
CONVENTION = "S = eta^-1 times the node/retained-input correlator matrix"


def ordinary_recursion(target, names, weights):
    """Exact exploratory recurrence; Lean independently proves and evaluates it."""
    rank = len(names)
    zero = tuple(tuple(Fraction(0) for _ in names) for _ in names)
    identity = tuple(tuple(Fraction(i == j) for j in range(rank)) for i in range(rank))
    cup = [[Fraction(0) for _ in names] for _ in names]
    index = {name: i for i, name in enumerate(names)}
    cup[index["H"]][index["unit"]] = 3
    cup[index["pt"]][index["H"]] = 3
    for name in names:
        if name.startswith("E"):
            cup[index[name]][index["unit"]] = -1
            cup[index["pt"]][index[name]] = 1

    def mul(a, b):
        return [[sum(a[i][k] * b[k][j] for k in range(rank)) for j in range(rank)]
                for i in range(rank)]

    @functools.lru_cache(None)
    def coefficient(power, beta):
        if power == 0:
            return identity if not any(beta) else zero
        if power == 1:
            return tuple(map(tuple, expected_matrix(target, beta, names)))
        if not any(beta):
            return zero
        result = [[-q for q in row] for row in mul(coefficient(power - 1, beta), cup)]
        for main in itertools.product(*(range(b + 1) for b in beta)):
            tail = tuple(b - a for a, b in zip(main, beta))
            if not any(tail):
                continue
            primary = cup if not any(main) else [
                [sum(a * w for a, w in zip(main, weights)) * q for q in row]
                for row in expected_matrix(target, main, names)]
            term = mul(primary, coefficient(power - 1, tail))
            result = [[a + b for a, b in zip(ar, br)] for ar, br in zip(result, term)]
        energy = sum(a * w for a, w in zip(beta, weights))
        return tuple(tuple(Fraction(q) / energy for q in row) for row in result)

    return coefficient


def explore(producer, pin):
    from sage.all import Fan, LaurentPolynomialRing, PolynomialRing, QQ, ZZ, matrix
    from sage.version import version
    from admcycles.admcycles import set_online_lookup, set_online_lookup_default

    codec.require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
                  "Review the exploration environment pin")
    set_online_lookup(False)
    set_online_lookup_default(False)
    sys.path.insert(0, str(producer))
    import gkm_localization
    from gkm_localization import StableMapsGKM, toric_target_from_fan
    codec.require(Path(gkm_localization.__file__).resolve().parent == producer / "gkm_localization",
                  "Imported a different producer")
    frames = {f["target"]: f for f in json.loads(INPUT.read_text())["targets"]}
    P = PolynomialRing(QQ, names=("x", "y"))
    K = P.fraction_field()
    R = LaurentPolynomialRing(ZZ, names=("x", "y"))

    def rational(q):
        q = QQ(q)
        return [int(q.numerator()), int(q.denominator())]

    def decode(q):
        def poly(terms):
            return sum(QQ(n) / QQ(d) * P.gen(0)**i * P.gen(1)**j
                       for (i, j), (n, d) in terms)
        return K(poly(q["numerator"])) / K(poly(q["denominator"]))

    def encode(q):
        q = K(q)
        def poly(p):
            return [[list(map(int, powers)), rational(c)] for powers, c in sorted(p.dict().items())]
        return {"numerator": poly(q.numerator()), "denominator": poly(q.denominator())}

    def ordinary(q):
        q = K(q)
        codec.require(q.denominator()(0, 0) != 0, "Unresolved ordinary pole")
        return QQ(q.numerator()(0, 0) / q.denominator()(0, 0))

    cases = []
    for spec in target_specifications():
        frame = frames[spec["id"]]
        target = toric_target_from_fan(Fan(cones=spec["cones"], rays=spec["rays"]), R,
                                      curve_basis=spec["curves"], name=frame["target"])
        points = [tuple(p) for p in frame["points"]]
        codec.require(points == sorted(target.fixed_points()), "Changed fixed-point indexing")
        codec.require(frame["rays"] == [list(ray) for ray in spec["rays"]], "Changed fan")
        basis = [target.cohomology_class({p: R(decode(frame["basis_to_fixedpoint"][j][i]))
                                         for j, p in enumerate(points)})
                 for i in range(len(frame["basis"]))]
        inverse = matrix(K, [[decode(q) for q in row] for row in frame["inverse_metric"]])
        expected = ordinary_recursion(frame["target"], frame["basis"], frame["energy_weights"])
        maps = StableMapsGKM(target)
        for power, beta in REQUESTS[frame["target"]]:
            print(f"Localizing {frame['target']} class {beta}, power {power}", file=sys.stderr, flush=True)
            paired = matrix(K, [[maps.integrate(0, 2, (ZZ ** len(beta))(beta),
                                               [(0, x), (power - 1, y)]) for y in basis] for x in basis])
            raised = inverse * paired
            specialized = [[ordinary(q) for q in row] for row in raised.rows()]
            claim = [[QQ(q.numerator) / QQ(q.denominator) for q in row]
                     for row in expected(power, beta)]
            codec.require(specialized == claim, f"Higher-calibration mismatch: {frame['target']} {beta} {power}")
            cases.append({"target": frame["target"], "class": list(beta), "basis": frame["basis"],
                          "inverse_loop_power": power, "tail_psi_power": power - 1,
                          "energy": sum(a * w for a, w in zip(beta, frame["energy_weights"])),
                          "paired_equivariant": [[encode(q) for q in row] for row in paired.rows()],
                          "operator_equivariant": [[encode(q) for q in row] for row in raised.rows()],
                          "operator_ordinary": [[rational(q) for q in row] for row in specialized]})
    return {"schema_version": 1, "kind": "gkm_localization.higher_calibration_comparison",
            "source": pin, "input_sha256": hashlib.sha256(INPUT.read_bytes()).hexdigest(),
            "environment": {"sage": version, "admcycles": "1.4"},
            "coefficient_convention": CONVENTION, "primary_deformation": "zero",
            "online_lookup": False, "cache_ephemeral": True, "cases": cases}


def read_report(raw):
    report = json.loads(raw, object_pairs_hook=codec.unique_object)
    source = json.loads(INPUT.read_text())
    codec.require(type(report["schema_version"]) is int and report["schema_version"] == 1 and
                  report["kind"] == "gkm_localization.higher_calibration_comparison", "Wrong schema")
    codec.require(report["input_sha256"] == hashlib.sha256(INPUT.read_bytes()).hexdigest() and
                  report["source"] == source["source"], "Changed source provenance")
    codec.require(report["environment"] == {"sage": "10.9", "admcycles": "1.4"}, "Wrong environment")
    codec.require(report["coefficient_convention"] == CONVENTION and
                  report["primary_deformation"] == "zero", "Changed convention")
    frames = {f["target"]: f for f in source["targets"]}
    grouped = {t: [] for t, _, _ in TARGETS}
    for case in report["cases"]:
        codec.require(case["target"] in grouped, "Unknown target")
        frame = frames[case["target"]]
        codec.require(case["basis"] == frame["basis"], "Changed basis order")
        beta = tuple(map(codec.integer, case["class"]))
        power = codec.integer(case["inverse_loop_power"])
        codec.require((power, beta) in REQUESTS[case["target"]] and
                      codec.integer(case["tail_psi_power"]) == power - 1, "Changed request or index")
        codec.require(codec.integer(case["energy"]) == sum(a * w for a, w in zip(beta, frame["energy_weights"])),
                      "Changed energy")
        rank = len(frame["basis"])
        inverse = codec.matrix(frame["inverse_metric"], rank)

        def decoded(key):
            data = case[key]
            codec.require(isinstance(data, list) and len(data) == rank and
                          all(isinstance(row, list) and len(row) == rank for row in data), "Wrong shape")
            for row in data:
                for q in row:
                    codec.require(set(q) == {"numerator", "denominator"}, "Wrong function fields")
            return [[codec.RationalFunction(codec.polynomial(q["numerator"]), codec.polynomial(q["denominator"]))
                     for q in row] for row in data]

        paired, raised = decoded("paired_equivariant"), decoded("operator_equivariant")
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
        received = [(c["inverse_loop_power"], tuple(c["class"])) for c in cases]
        codec.require(len(received) == len(set(received)) and set(received) == set(REQUESTS[target]),
                      "Incomplete or duplicate request coverage")
    return report, grouped


def emit(raw):
    _, grouped = read_report(raw)
    lines = ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
             "Released under Apache 2.0 license as described in the file LICENSE.",
             "Authors: JMA", "-/", "module", "",
             "public import AxiomaticGW.Surfaces.Fixtures.HigherCalibration", "",
             "/-!", "# Native GKM higher-calibration replay", "",
             "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
             "Actual incoming matrices are checked against the derived recursion.",
             "The digest records provenance; it is not a proof of localization geometry.", "-/", "",
             "@[expose] public section", "", "namespace AxiomaticGW.GKM.HigherCalibrationReplay", ""]
    label = {"unit": ".unit", "H": ".hyperplane", "E1": ".exceptional 0", "E2": ".exceptional 1", "pt": ".point"}
    stacked = lambda xs: "![" + ",\n    ".join(xs) + "]"
    for target, namespace, surface in TARGETS:
        cases = grouped[target]
        n, rank = len(cases), len(cases[0]["basis"])
        lines += [f"namespace {namespace}", "", "/-- Incoming powers and full curve coordinates. -/",
                  f"def requests : Fin {n} → ℕ × SurfaceTarget.Curve .{surface} :=",
                  "  " + stacked([f"({c['inverse_loop_power']}, {vector(list(map(str, c['class'])))})" for c in cases]), "",
                  "/-- Incoming basis order. -/", f"def labels : Fin {rank} → SurfaceBasisLabel .{surface} :=",
                  "  " + vector([label[x] for x in cases[0]["basis"]]), "",
                  "/-- Actual imported ordinary matrices. -/",
                  f"def entries : Fin {n} → Matrix (Fin {rank}) (Fin {rank}) ℚ :=",
                  "  " + stacked([rational_matrix(c["operator_ordinary"], rank, rank) for c in cases]), "",
                  "/-- Actual incoming cotangent powers. -/", f"def psiPowers : Fin {n} → ℕ :=",
                  "  " + vector([str(c["tail_psi_power"]) for c in cases]), "",
                  "theorem labels_bijective : Function.Bijective labels := by decide +kernel", "",
                  "/-- Requests agree with the separately held benchmark suite. -/",
                  "theorem coverage : Finset.univ.image requests =",
                  f"    (SurfaceHigherCalibration.requests .{surface}).toFinset := by decide +kernel", "",
                  "theorem indices : ∀ i, psiPowers i + 1 = (requests i).1 := by decide +kernel", "",
                  "/-- Each incoming entry is checked at its actual class and loop power. -/",
                  "theorem accepted : ∀ i row col, entries i row col =",
                  f"    SurfaceDescendant.reconstructedCalibrationMatrix .{surface}",
                  "      (requests i).1 (requests i).2 (labels row) (labels col) := by", "  decide +kernel", "",
                  f"end {namespace}", ""]
    return "\n".join(lines + ["end AxiomaticGW.GKM.HigherCalibrationReplay", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    explore_parser = commands.add_parser("explore")
    explore_parser.add_argument("--producer", required=True, type=Path)
    explore_parser.add_argument("--output", required=True, type=Path)
    replay = commands.add_parser("replay")
    replay.add_argument("report", type=Path)
    replay.add_argument("--output", required=True, type=Path)
    replay.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.command == "explore":
        producer, pin = producer_source(args.producer)
        with tempfile.TemporaryDirectory(prefix="gw-higher-calibration-") as directory:
            os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
            for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
                cache = Path(directory) / name
                cache.mkdir()
                os.environ[name] = str(cache)
            (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
            report = explore(producer, pin)
        args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    else:
        result = emit(args.report.read_bytes())
        if args.check:
            codec.require(args.output.read_text() == result, "Saved replay differs from generated source")
        else:
            args.output.write_text(result)


if __name__ == "__main__":
    main()
