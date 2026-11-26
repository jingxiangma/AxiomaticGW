#!/usr/bin/env python3
"""Finite exact WDVV pivot/decrease probes, not a proof of a uniform recursion.

The input is the pinned admcycles-derived three-column frame. Shared graph and
component rules generate candidate equations; no GW values are substituted.
"""

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import export_surface_equations as exchange


FRAME = exchange.ROOT / "environments/wdvv-candidate-osx-arm64.json"
FRAME_SHA256 = "44ba7410c29fd82126c188d52e0203f7aaa38139c315c7317e6221a6d905284d"
TARGETS = (("P2", (3,)), ("F1", (1, 2)), ("Bl2P2", (1, 1, 1)))


def energy(weights, curve):
    return sum(w * b for w, b in zip(weights, curve))


def explore(bound):
    if type(bound) is not int or bound < 3:
        raise ValueError("The energy bound must be an integer at least three")
    pins = {FRAME: FRAME_SHA256}
    pins.update({exchange.ROOT / "scripts" / p: h for p, h in exchange.HELPER_SHA256.items()})
    for path, expected in pins.items():
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f"Pinned source changed: {path.name}")
    frame = json.loads(FRAME.read_bytes())
    cases = []
    for target, weights in TARGETS:
        for curve in product(range(bound + 1), repeat=len(weights)):
            e = energy(weights, curve)
            if not 3 <= e <= bound or (target == "P2" and curve == (1,)):
                continue
            if target == "P2":
                labels, extra, pivot = (1, 1, 2, 2), e - 4, 1
            elif curve[-1] > 0:
                labels, extra, pivot = (1, 2, 3, 3), e - 3, -curve[-1]
            else:
                i = next(i for i, b in enumerate(curve[:-1]) if b)
                labels, extra, pivot = (1, 1, 2, 3 + i), e - 3, -curve[i]
            columns = exchange.expanded_columns(frame, target, curve, extra, labels,
                                                expected_columns=3)
            coefficients = defaultdict(Fraction)
            for column in columns:
                for monomial, coefficient in column:
                    coefficients[tuple(monomial)] += Fraction(*coefficient)
            coefficients = {m: c for m, c in coefficients.items() if c}
            query = ("query", 0, curve, ((2, 0),) * (e - 1))
            actual = coefficients.pop((query,), Fraction())
            for monomial in coefficients:
                for v in monomial:
                    ve = energy(weights, v[2])
                    if not (v[0] == "query" and v[1] == 0 and 0 < ve < e
                            and len(v[2]) == len(weights)
                            and v[3] == ((2, 0),) * (ve - 1)):
                        raise ValueError(f"Residual query does not decrease: {target}, {curve}, {v}")
            if actual != pivot or pivot == 0:
                raise ValueError(f"Unexpected pivot: {target}, {curve}, {actual}, expected {pivot}")
            cases.append({"target": target, "curve": curve, "energy": e,
                          "extra_markings": extra, "original_labels": labels,
                          "added_labels": [2] * extra, "powers": [0] * (4 + extra),
                          "pivot": [pivot, 1], "residual_terms": len(coefficients),
                          "residuals_are_positive_lower_energy_point_queries": True})
    sources = set(pins) | {Path(__file__).resolve(), Path(exchange.__file__).resolve()}
    return {
        "schema_version": 1,
        "status": "finite_exploration_only",
        "energy_bound": bound,
        "coverage": "All full nonnegative curve coordinates with energy 3 through the bound, "
                    "excluding the plane line seed; energy-one/two base cases are separate.",
        "counts": dict(Counter(c["target"] for c in cases)),
        "sources_sha256": {str(p.relative_to(exchange.ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in sorted(sources)},
        "cases": cases,
        "uniform_claim_proved": False,
        "limitations": ["Shared-source symbolic exploration, not independent GW computation.",
                        "No numerical GW values or benchmark table are computed.",
                        "Lean must still prove uniform coefficient isolation and decreasing calls.",
                        "Geometric applicability, descendants and genus two are not established."],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--energy-bound", type=int, default=12)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = explore(args.energy_bound)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed {len(report['cases'])} finite pivot/decrease probes", flush=True)


if __name__ == "__main__":
    main()
