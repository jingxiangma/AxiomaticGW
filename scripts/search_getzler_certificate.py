#!/usr/bin/env python3
"""Explore the fixed Getzler graph frame and search an exact raw consequence.

Sage/admcycles supplies candidate coordinates and intersection diagnostics.
Lean independently fixes the graph frame, normalization, source row, and claim.
The geometric relation is Getzler, Theorem 1.8; no Sage zero flag proves it.
"""

import hashlib
import importlib.metadata
from itertools import combinations, permutations
import json
import os
from pathlib import Path
import platform
import sys
import tempfile

from export_admcycles_certificate import require


def run_search():
    from sage.all import QQ, matrix, vector
    from sage.version import version
    from admcycles import StableGraph, TautologicalRing
    from admcycles import admcycles, stable_graph, tautological_ring

    require(version == "10.9", "Review the Sage pin")
    require(importlib.metadata.version("admcycles") == "1.4", "Review the admcycles pin")
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices,
            admcycles.genstobasis, admcycles.FZ_conjecture_holds)), "Online lookup active")
    ring = TautologicalRing(1, 4, moduli="st", base_ring=QQ)
    kinds = ["delta22"] * 3 + ["delta23"] * 12 + ["delta24"] * 6 + ["delta34"] * 4
    kinds += ["delta03"] * 4 + ["delta04"] + ["deltaBeta"] * 3
    assignments = [[1, 1, 2, 2], [1, 2, 1, 2], [1, 2, 2, 1]]
    for pair in combinations(range(4), 2):
        for extra in range(4):
            if extra not in pair:
                assignments.append([2 if x in pair else 1 if x == extra else 0
                                    for x in range(4)])
    for pair in combinations(range(4), 2):
        assignments.append([2 if x in pair else 1 for x in range(4)])
    assignments += [[1 if x == omitted else 2 for x in range(4)] for omitted in range(4)]
    assignments += [[0 if x == omitted else 1 for x in range(4)] for omitted in range(4)]
    assignments += [[1] * 4, [0, 0, 1, 1], [0, 1, 0, 1], [0, 1, 1, 0]]
    graphs, raw_classes, raw_indices, factors = [], [], [], []
    for index, assignment in enumerate(assignments):
        genera = [1, 0, 0] if index < 25 else [0, 0]
        endpoints = ([[0, 1], [0, 2]] if index < 3 else [[0, 1], [1, 2]])
        if index >= 25:
            endpoints = [[0, 0], [0, 1]] if index < 30 else [[0, 1], [0, 1]]
        legs = [[] for _ in genera]
        for label, vertex in enumerate(assignment, 1):
            legs[vertex].append(label)
        for edge, pair in enumerate(endpoints):
            for branch, vertex in enumerate(pair):
                legs[vertex].append(5 + 2 * edge + branch)
        source = StableGraph(genera, legs, [(5, 6), (7, 8)])
        raw = ring(source)
        require(len(raw._terms) == 1, "Expected one undecorated raw term")
        term = next(iter(raw._terms.values()))
        graph = term.gamma
        require(list(term.poly.coeff) == [1], "Unexpected raw normalization")
        kappa, psi = term.poly.monom[0]
        require(all(not any(row) for row in kappa) and not any(psi.values()),
                "Unexpected decoration")
        order = int(graph.automorphism_number())
        require(order == (1 if index < 25 else 2), "Unexpected graph automorphism")
        factor = QQ(1) / order
        factors.append(factor)
        graphs.append({"index": index, "genus": [int(g) for g in graph.genera()],
                       "leg_vertices": [int(graph.vertex(s)) for s in range(1, 5)],
                       "endpoints": [[int(graph.vertex(s)) for s in pair]
                                     for pair in graph.edges()],
                       "kappa": [[0, 0] for _ in genera], "leg_psi": [0] * 4,
                       "half_psi": [[0, 0], [0, 0]]})
        raw_vector = raw.vector(2)
        selected = [j for j, q in enumerate(raw_vector) if q]
        require(len(selected) == 1 and raw_vector[selected[0]] == 1,
                "Expected a raw unit coordinate")
        require(ring.from_vector(raw_vector, 2).vector(2) == raw_vector,
                "Raw coordinate round-trip failed")
        raw_indices.append(selected[0])
        raw_classes.append(raw)
    require(len(set(raw_indices)) == 33, "Duplicate marked graph columns")

    names = ["delta22", "delta23", "delta24", "delta34", "delta03", "delta04", "deltaBeta"]
    cycles = [sum((factor * raw for raw, factor, kind in zip(raw_classes, factors, kinds)
                   if kind == name), ring.zero()) for name in names]
    orbit_counts = []
    for name in names:
        first = kinds.index(name)
        orbit = {tuple(raw_classes[first].rename_legs(
            dict(zip(range(1, 5), permutation)), inplace=False).vector(2))
                 for permutation in permutations(range(1, 5))}
        expected = {tuple(raw.vector(2)) for raw, kind in zip(raw_classes, kinds) if kind == name}
        require(orbit == expected, "Incomplete or duplicated marking orbit")
        orbit_counts.append(len(orbit))
    require(orbit_counts == [3, 12, 6, 4, 4, 1, 3], "Wrong orbit sizes")

    # Independent published normalization diagnostic, not a proof of relation validity.
    published = matrix(QQ, [[QQ(1)/8, 0, 0, 0, 0, QQ(3)/2, QQ(3)/2],
        [0, 0, 0, 0, -6, 6, 0], [0, 0, 0, -QQ(1)/2, 6, -3, 0],
        [0, 0, -QQ(1)/2, QQ(1)/6, -2, 0, 0], [0, -6, 6, -2, 0, 0, 0],
        [QQ(3)/2, 6, -3, 0, 0, 0, 0], [QQ(3)/2, 0, 0, 0, 0, 0, 9]])
    computed = matrix(QQ, [[(left * right).evaluate() for right in cycles] for left in cycles])
    require(computed == published, "Getzler intersection normalization mismatch")
    coefficients = dict(zip(names, (12, -4, -2, 6, 1, 1, -2)))
    require(computed * vector(QQ, [coefficients[n] for n in names]) == 0,
            "Published relation failed intersection diagnostic")
    claim_coefficients = dict(zip(names, (-3, 1, QQ(1)/2, -QQ(3)/2,
                                          -QQ(1)/4, -QQ(1)/4, QQ(1)/2)))
    rows = matrix(QQ, [[coefficients[name] * factor for name, factor in zip(kinds, factors)]])
    requested = vector(QQ, [claim_coefficients[name] * factor
                            for name, factor in zip(kinds, factors)])
    witness = rows.solve_left(requested)
    require(witness * rows == requested, "Invalid exact searched witness")
    rational = lambda q: [int(QQ(q).numerator()), int(QQ(q).denominator())]
    return {
        "schema_version": 1, "frame": "getzler_mbar_1_4_v1", "locus": "full_stable",
        "genus": 1, "markings": [0, 1, 2, 3], "codimension": 2,
        "normalization": "raw_gluing_pushforward",
        "source_label_map": [[1, 0], [2, 1], [3, 2], [4, 3]],
        "relation_ids": ["getzler_1_8"],
        "relation_source": "10.1090/S0894-0347-97-00246-4; Theorem 1.8",
        "graphs": graphs, "column_factors": [[1, 1]] * 33,
        "orbifold_factors": [rational(q) for q in factors], "stratum_ids": kinds,
        "rows": [[rational(q) for q in row] for row in rows],
        "requested": [rational(q) for q in requested],
        "witness": [rational(q) for q in witness],
        "environment": {"sage": version, "admcycles": "1.4",
                        "python": platform.python_version(), "architecture": platform.machine()},
        "producer_source_sha256": {Path(m.__file__).name:
            hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
            for m in (admcycles, stable_graph, tautological_ring)},
        "exploration": {"raw_column_indices": raw_indices, "marking_orbit_sizes": orbit_counts,
                        "intersection_matrix": [[rational(q) for q in row] for row in computed],
                        "intersection_rank": int(computed.rank()),
                        "cache_ephemeral": True, "online_lookup": False},
        "scope": "Exact candidate graphs, normalization diagnostics, and a searched witness. "
                 "Geometric Getzler validity remains an explicit Lean input.",
    }


def main():
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-getzler-search-") as temporary:
        for variable, name in (("DOT_SAGE", "sage"), ("ADMCYCLES_CACHE_DIR", "admcycles"),
                               ("MPLCONFIGDIR", "matplotlib"), ("XDG_CACHE_HOME", "xdg")):
            location = Path(temporary) / name
            location.mkdir()
            os.environ[variable] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        print(json.dumps(run_search(), indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"Getzler search failed: {error}", file=sys.stderr)
        sys.exit(1)
