#!/usr/bin/env python3
"""Search exact exceptional-class Getzler equations with Sage.

The pinned 33-column relation comes from the existing admcycles workflow.
This script expands basis-labelled requests and solves a finite rational
system. Its output is exploration, not a proof of geometric applicability.
The separate Lean fixture checks the complete nine selected expansions.
"""

import argparse
from collections import defaultdict
import hashlib
from itertools import combinations_with_replacement
import json
import os
from pathlib import Path
import platform
import sys
import tempfile

sys.dont_write_bytecode = True
import export_surface_equations as exchange


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, (list, tuple)) else value


def collect(frame, target, curve, labels, QQ):
    columns = exchange.expanded_columns(frame, target, curve, 0, labels)
    coefficients = defaultdict(lambda: QQ(0))
    for column in columns:
        for monomial, (numerator, denominator) in column:
            coefficients[freeze(monomial)] += QQ(numerator) / denominator
    return {m: c for m, c in sorted(coefficients.items()) if c}, list(map(len, columns))


def pair(c):
    return [int(c.numerator()), int(c.denominator())]


def point(genus, curve, count):
    return "query", genus, tuple(curve), ((2, 0),) * count


def explore(QQ, matrix, version):
    pins = {exchange.FRAME: exchange.FRAME_SHA256}
    pins.update({exchange.ROOT / "scripts" / name: sha
                 for name, sha in exchange.HELPER_SHA256.items()})
    for path, expected in pins.items():
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f"Pinned exploration input changed: {path.name}")
    frame = json.loads(exchange.FRAME.read_bytes())
    cases = []
    targets = (("F1", (1, 0), 0), ("Bl2P2", (1, 0, 0), 0),
               ("Bl2P2", (0, 1, 0), 1))
    for target, exceptional, index in targets:
        double = tuple(2 * b for b in exceptional)
        state = 3 + index
        unknowns = ((point(0, exceptional, 0), point(1, exceptional, 1)),
                    (point(0, double, 1),), (point(1, double, 2),))
        rows = []
        for labels in ((1, 1, 1, 1), (1, state, state, state), (1, 1, state, state)):
            coefficients, counts = collect(frame, target, double, labels, QQ)
            if not set(coefficients) <= set(unknowns):
                raise ValueError("An additional unknown remains in the selected equation")
            rows.append([coefficients.get(m, QQ(0)) for m in unknowns])
            cases.append({"target": target, "curve": double, "original_labels": labels,
                          "extra_markings": 0, "powers": [0, 0, 0, 0],
                          "column_contributions": counts,
                          "terms": [[m, pair(c)] for m, c in coefficients.items()]})
        system = matrix(QQ, rows)
        expected = matrix(QQ, [[0, 0, -9], [0, -QQ(3) / 2, 0], [3, -QQ(1) / 6, 3]])
        if system != expected or system.rank() != 3:
            raise ValueError("The expected three-equation system was not recovered")
    # These dimension-compatible primary basis multisets give no useful
    # equation directly at energy one. This is a finite diagnostic only.
    probes = []
    for target, curve, _ in targets + (("Bl2P2", (0, 0, 1), 2),):
        tested = 0
        nonzero = []
        for labels in combinations_with_replacement(range(len(curve) + 2), 4):
            if sum({0: 0, 1: 1, 2: 2}.get(s, 1) for s in labels) != 3:
                continue
            tested += 1
            coefficients, _ = collect(frame, target, curve, labels, QQ)
            if coefficients:
                nonzero.append({"labels": labels,
                                "terms": [[m, pair(c)] for m, c in coefficients.items()]})
        probes.append({"target": target, "curve": curve,
                       "tested_basis_multisets": tested, "nonzero_equations": nonzero})
    sources = {str(path.relative_to(exchange.ROOT)): sha for path, sha in pins.items()}
    for path in (Path(__file__), Path(exchange.__file__)):
        sources[str(path.resolve().relative_to(exchange.ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return {"schema_version": 1, "status": "exploration_only",
            "sage_version": version, "python_version": platform.python_version(),
            "machine": platform.machine(), "sources_sha256": sources,
            "unknown_order": ["N0(E;0) * N1(E;1)", "N0(2E;1)", "N1(2E;2)"],
            "coefficient_matrix": [[pair(c) for c in row] for row in expected.rows()],
            "rank": int(expected.rank()), "determinant": pair(expected.det()),
            "cases": cases, "energy_one_probes": probes,
            "limitations": ["Finite exact coefficient search; not a geometric GW computation.",
                            "Lean checks each selected graph expansion independently.",
                            "Geometric laws and finite seeds remain explicit inputs.",
                            "The class L is probed but its GW values are not reconstructed."]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="gw-exceptional-sage-") as cache:
        os.environ["DOT_SAGE"] = cache
        from sage.all import QQ, matrix
        from sage.version import version
        if version != "10.9":
            raise RuntimeError("This exploration is pinned to Sage 10.9")
        args.output.write_text(json.dumps(explore(QQ, matrix, version), indent=2) + "\n")


if __name__ == "__main__":
    main()
