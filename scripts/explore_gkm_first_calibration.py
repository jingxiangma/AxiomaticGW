#!/usr/bin/env python3
"""Compare every first calibration matrix through energy three with native GKM.

The Lean theorem proves uniform vanishing above energy three. These native
localization results are independent numerical checks of that finite sector,
not proofs of CohFT classes, the localization formula or symplecticity.
"""

import argparse
import hashlib
import importlib.metadata
import itertools
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
from export_gkm_inputs import producer_source, require, target_specifications

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "environments/gkm-inputs-osx-arm64.json"


def expected_matrix(target, beta, names):
    """Sparse claims also held by SurfaceFirstCalibration.values in Lean."""
    result = [[0 for _ in names] for _ in names]
    index = {name: i for i, name in enumerate(names)}

    def put(row, col, value):
        result[index[row]][index[col]] = value

    line = {"X0": (1,), "X1": (1, 1), "X2": (1, 1, 1)}[target]
    exceptional = {"X0": {}, "X1": {(1, 0): "E1"},
                   "X2": {(1, 0, 0): "E1", (0, 1, 0): "E2"}}[target]
    fibers = {"X0": {}, "X1": {(0, 1): "E1"},
              "X2": {(0, 1, 1): "E1", (1, 0, 1): "E2"}}[target]
    if beta == line:
        put("unit", "pt", 1)
    elif beta in exceptional:
        put(exceptional[beta], exceptional[beta], -1)
    elif beta in fibers:
        e = fibers[beta]
        for row, col, value in [("unit", "H", 1), ("unit", e, 1),
                                ("H", "pt", 1), (e, "pt", -1)]:
            put(row, col, value)
    elif target == "X2" and beta == (0, 0, 1):
        for row in ("H", "E1", "E2"):
            for col in ("H", "E1", "E2"):
                put(row, col, 1 if row == "H" else -1)
    return result


def explore(producer, pin):
    from sage.all import Fan, LaurentPolynomialRing, PolynomialRing, QQ, ZZ, matrix
    from sage.version import version
    from admcycles.admcycles import set_online_lookup, set_online_lookup_default

    require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
            "Review the Sage/admcycles environment pin")
    set_online_lookup(False)
    set_online_lookup_default(False)
    sys.path.insert(0, str(producer))
    import gkm_localization
    from gkm_localization import StableMapsGKM, toric_target_from_fan
    require(Path(gkm_localization.__file__).resolve().parent == producer / "gkm_localization",
            "Imported a different producer package")
    source = json.loads(INPUT.read_text())
    frames = {frame["target"]: frame for frame in source["targets"]}
    P = PolynomialRing(QQ, names=("x", "y"))
    K = P.fraction_field()
    R = LaurentPolynomialRing(ZZ, names=("x", "y"))

    def rational(q):
        q = QQ(q)
        return [int(q.numerator()), int(q.denominator())]

    def polynomial(terms):
        return sum(QQ(n) / QQ(d) * P.gen(0)**i * P.gen(1)**j
                   for (i, j), (n, d) in terms)

    def decode(value):
        return K(polynomial(value["numerator"])) / K(polynomial(value["denominator"]))

    def encode(value):
        value = K(value)
        terms = lambda poly: [[list(map(int, powers)), rational(c)]
                              for powers, c in sorted(poly.dict().items())]
        return {"numerator": terms(value.numerator()), "denominator": terms(value.denominator())}

    def ordinary(value):
        value = K(value)
        denominator = value.denominator()(0, 0)
        require(denominator != 0, "Unresolved pole in the ordinary operator coefficient")
        return QQ(value.numerator()(0, 0) / denominator)

    cases = []
    for specification in target_specifications():
        frame = frames[specification["id"]]
        target = toric_target_from_fan(Fan(cones=specification["cones"], rays=specification["rays"]),
                                      R, curve_basis=specification["curves"], name=frame["target"])
        points = [tuple(p) for p in frame["points"]]
        require(points == sorted(target.fixed_points()), "Fixed-point indexing changed")
        require(frame["rays"] == [list(ray) for ray in specification["rays"]], "Fan mismatch")
        basis = [target.cohomology_class({p: R(decode(frame["basis_to_fixedpoint"][j][i]))
                                         for j, p in enumerate(points)})
                 for i in range(len(frame["basis"]))]
        eta_inverse = matrix(K, [[decode(x) for x in row] for row in frame["inverse_metric"]])
        weights = frame["energy_weights"]
        maps = StableMapsGKM(target)
        for beta in itertools.product(*(range(3 // w + 1) for w in weights)):
            energy = sum(a * w for a, w in zip(beta, weights))
            if energy == 0 or energy > 3:
                continue
            print(f"Localizing {frame['target']} class {beta}", file=sys.stderr, flush=True)
            paired = matrix(K, [[maps.integrate(0, 2, (ZZ ** len(beta))(beta), [(0, x), (0, y)])
                                 for y in basis] for x in basis])
            raised = eta_inverse * paired
            specialized = [[ordinary(q) for q in row] for row in raised.rows()]
            expected = expected_matrix(frame["target"], beta, frame["basis"])
            require(specialized == expected, f"Calibration discrepancy: {frame['target']} {beta}")
            cases.append({"target": frame["target"], "class": list(beta), "energy": energy,
                          "basis": frame["basis"], "inverse_loop_power": 1, "tail_psi_power": 0,
                          "paired_equivariant": [[encode(q) for q in row] for row in paired.rows()],
                          "operator_equivariant": [[encode(q) for q in row] for row in raised.rows()],
                          "operator_ordinary": [[rational(q) for q in row] for row in specialized],
                          "expected_ordinary": expected, "matches": True})
    require(len(cases) == 25, "Incomplete first-coefficient class coverage")
    return {"schema_version": 1, "kind": "gkm_localization.first_calibration_comparison",
            "source": pin, "input_sha256": hashlib.sha256(INPUT.read_bytes()).hexdigest(),
            "environment": {"sage": version, "admcycles": "1.4"},
            "coefficient_convention": "S = eta^-1 times the node/retained-input correlator matrix",
            "primary_deformation": "zero", "online_lookup": False, "cache_ephemeral": True,
            "coverage": {"classes": 25, "matrix_entries": sum(len(c['basis'])**2 for c in cases),
                         "all_positive_classes_through_energy": 3},
            "scope": "Native numerical localization versus the complete Lean first-coefficient table. "
                     "State and curve conventions are shared. This does not certify CohFT classes, "
                     "localization geometry, higher calibration powers or symplecticity.",
            "cases": cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--producer", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    producer, pin = producer_source(args.producer)
    with tempfile.TemporaryDirectory(prefix="gw-first-calibration-") as directory:
        os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
        for variable in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            cache = Path(directory) / variable
            cache.mkdir()
            os.environ[variable] = str(cache)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        report = explore(producer, pin)
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")


if __name__ == "__main__":
    main()
