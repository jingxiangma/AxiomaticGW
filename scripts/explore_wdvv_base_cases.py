#!/usr/bin/env python3
"""Explore surface base cases using pinned WDVV/Getzler frames and exact Sage algebra.

Shared graph and component data are exploration inputs. Separate Lean fixtures
check complete expansions, and numerical theorems retain geometric hypotheses.
No computed value is added to the project's finite seed package.
"""

import argparse
from collections import defaultdict
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
import export_surface_equations as exchange


WDVV = exchange.ROOT / "environments/wdvv-candidate-osx-arm64.json"
WDVV_SHA256 = "44ba7410c29fd82126c188d52e0203f7aaa38139c315c7317e6221a6d905284d"
REQUESTS = (
    ("plane_conic", "WDVV", "P2", (2,), 2, (1, 1, 2, 2)),
    ("hirzebruch_line", "WDVV", "F1", (1, 1), 0, (1, 2, 3, 3)),
    ("blowup_mixed_line", "WDVV", "Bl2P2", (1, 1, 1), 0, (1, 1, 2, 3)),
    ("blowup_line", "WDVV", "Bl2P2", (1, 1, 1), 0, (1, 2, 3, 3)),
    ("blowup_ruling_0", "WDVV", "Bl2P2", (1, 0, 1), 0, (1, 1, 3, 3)),
    ("blowup_ruling_1", "WDVV", "Bl2P2", (0, 1, 1), 0, (1, 1, 4, 4)),
    ("strict_line_four_h", "Getzler", "Bl2P2", (0, 0, 2), 0, (1, 1, 1, 1)),
    ("strict_line_three_h", "Getzler", "Bl2P2", (0, 0, 2), 0, (1, 1, 1, 3)),
    ("strict_line_one_h", "Getzler", "Bl2P2", (0, 0, 2), 0, (1, 3, 3, 3)),
)


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, (tuple, list)) else value


def pair(c):
    return [int(c.numerator()), int(c.denominator())]


def point(genus, curve, n):
    return "query", genus, tuple(curve), ((2, 0),) * n


def substitute(coefficients, values, QQ):
    result = defaultdict(lambda: QQ(0))
    for monomial, coefficient in coefficients.items():
        rest = []
        for v in monomial:
            if v in values:
                coefficient *= values[v]
            else:
                rest.append(v)
        result[tuple(rest)] += coefficient
    return {m: c for m, c in result.items() if c}


def linear_system(equations, unknowns, QQ, matrix, vector):
    if any(set(eq) - set(unknowns) - {()} for eq in equations):
        raise ValueError("An unaccounted monomial remains in the proposed system")
    coefficients = matrix(QQ, [[eq.get(m, 0) for m in unknowns] for eq in equations])
    rhs = vector(QQ, [-eq.get((), 0) for eq in equations])
    solution = coefficients.solve_right(rhs)
    return {"matrix": [[pair(c) for c in row] for row in coefficients.rows()],
            "rhs": [pair(c) for c in rhs], "rank": int(coefficients.rank()),
            "determinant": pair(coefficients.det()), "solution": [pair(c) for c in solution]}


def explore(QQ, matrix, vector, version):
    pins = {WDVV: WDVV_SHA256, exchange.FRAME: exchange.FRAME_SHA256}
    pins.update({exchange.ROOT / "scripts" / p: h for p, h in exchange.HELPER_SHA256.items()})
    for p, h in pins.items():
        if hashlib.sha256(p.read_bytes()).hexdigest() != h:
            raise ValueError(f"Pinned source changed: {p.name}")
    frames = {"WDVV": json.loads(WDVV.read_bytes()), "Getzler": json.loads(exchange.FRAME.read_bytes())}
    cases, equations = [], {}
    for name, relation, target, curve, extra, labels in REQUESTS:
        columns = exchange.expanded_columns(frames[relation], target, curve, extra, labels,
                                            expected_columns=3 if relation == "WDVV" else 33)
        result = defaultdict(lambda: QQ(0))
        for column in columns:
            for monomial, (num, den) in column:
                result[freeze(monomial)] += QQ(num) / den
        equations[name] = {m: c for m, c in sorted(result.items()) if c}
        cases.append({"id": name, "relation": relation, "target": target, "curve": curve,
                      "original_labels": labels, "extra_markings": extra,
                      "added_labels": [2] * extra, "powers": [0] * (4 + extra),
                      "column_contributions": list(map(len, columns)),
                      "terms": [[m, pair(c)] for m, c in equations[name].items()]})
    # Only the existing line and exceptional genus-zero seeds enter WDVV.
    conic = substitute(equations["plane_conic"], {point(0, (1,), 2): QQ(1)}, QQ)
    fiber = substitute(equations["hirzebruch_line"],
                       {point(0, (1, 1), 2): QQ(1), point(0, (1, 0), 0): QQ(1)}, QQ)
    seeds = {point(0, (1, 1, 1), 2): QQ(1), point(0, (1, 0, 0), 0): QQ(1),
             point(0, (0, 1, 0), 0): QQ(1)}
    lvar = point(0, (0, 0, 1), 0)
    blowup = [substitute(equations[name], seeds, QQ) for name in
              ("blowup_mixed_line", "blowup_line", "blowup_ruling_0", "blowup_ruling_1")]
    unknowns = ((lvar, point(0, (1, 1, 0), 1)), (point(0, (0, 1, 1), 1),),
                (lvar,), (point(0, (1, 0, 1), 1),))
    systems = {
        "plane_conic": linear_system([conic], ((point(0, (2,), 5),),), QQ, matrix, vector),
        "hirzebruch_fiber": linear_system([fiber], ((point(0, (0, 1), 1),),), QQ, matrix, vector),
        "blowup": linear_system(blowup, unknowns, QQ, matrix, vector),
    }
    if systems["blowup"]["solution"] != [[0, 1], [1, 1], [1, 1], [1, 1]]:
        raise ValueError("The original seeds did not determine the expected blowup base cases")
    # This substitution is a derived value, not an additional seed.
    strict = [substitute(equations[name], {lvar: QQ(1)}, QQ) for name in
              ("strict_line_four_h", "strict_line_three_h", "strict_line_one_h")]
    systems["strict_line"] = linear_system(strict,
        ((point(1, (0, 0, 1), 1),), (point(0, (0, 0, 2), 1),), (point(1, (0, 0, 2), 2),)),
        QQ, matrix, vector)
    if systems["strict_line"]["solution"] != [[0, 1]] * 3:
        raise ValueError("The derived L normalization did not give the three vanishings")
    sources = {str(p.relative_to(exchange.ROOT)): h for p, h in pins.items()}
    for p in (Path(__file__), Path(exchange.__file__)):
        sources[str(p.resolve().relative_to(exchange.ROOT))] = hashlib.sha256(p.read_bytes()).hexdigest()
    return {"schema_version": 1, "status": "exploration_only", "sage_version": version,
            "sources_sha256": sources, "cases": cases, "systems": systems,
            "blowup_unknown_order": ["N0(L)*N0(E1+E2;1)", "N0(E2+L;1)", "N0(L)", "N0(E1+L;1)"],
            "strict_line_unknown_order": ["N1(L;1)", "N0(2L;1)", "N1(2L;2)"],
            "limitations": ["Shared graph frame and component rules, not an independent GW computation.",
                            "Lean separately checks every complete selected expansion and numerical deduction.",
                            "Geometric compatibility and seed validity remain explicit inputs.",
                            "No uniform decreasing recursion or full benchmark coverage is asserted."]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="gw-wdvv-sage-") as cache:
        os.environ["DOT_SAGE"] = cache
        from sage.all import QQ, matrix, vector
        from sage.version import version
        if version != "10.9":
            raise RuntimeError("This exploration is pinned to Sage 10.9")
        args.output.write_text(json.dumps(explore(QQ, matrix, vector, version), indent=2) + "\n")


if __name__ == "__main__":
    main()
