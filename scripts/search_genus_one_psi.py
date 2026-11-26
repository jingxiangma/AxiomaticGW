#!/usr/bin/env python3
"""Search the Mbar(1,1) psi relation in the pinned full-stable 3-spin rows.

Retain the original generator parameters and raw graphs. Row-span arithmetic
and intersection diagnostics do not prove geometric vanishing of the rows.
"""

import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import tempfile

from export_admcycles_certificate import require


FRAME = "genus_one_psi_mbar_1_1_v1"
RELATION_SOURCE = "arXiv:1303.1043; admcycles 1.4 interior_FZ(1,1,(1,),MODULI_ST)"


def run_search():
    from sage.all import QQ, matrix, vector
    from sage.version import version
    from admcycles import StableGraph, TautologicalRing, admcycles, stable_graph, tautological_ring
    from admcycles.DR import algebra, relations
    from admcycles.DR.moduli import MODULI_ST

    require(version == "10.9", "Review the Sage pin")
    require(importlib.metadata.version("admcycles") == "1.4", "Review the admcycles pin")
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices,
            admcycles.genstobasis, admcycles.FZ_conjecture_holds)), "Online lookup active")
    ring = TautologicalRing(1, 1, moduli="st", base_ring=QQ)
    loop = StableGraph([0], [[1, 2, 3]], [(2, 3)])
    classes = [ring.kappa(1), ring.psi(1), ring(loop)]
    graphs, raw_vectors, automorphisms = [], [], []
    for index, element in enumerate(classes):
        require(len(element._terms) == 1, "Expected a single raw graph term")
        term = next(iter(element._terms.values()))
        require(list(term.poly.coeff) == [1], "Raw graph coefficient changed")
        require(len(term.poly.monom) == 1, "Expected a single decoration")
        kappa, psi = term.poly.monom[0]
        graph = term.gamma
        require(all(len(powers) <= 1 for powers in kappa), "Unexpected kappa degree")
        edges = graph.edges()
        graphs.append({"index": index, "genus": [int(g) for g in graph.genera()],
                       "leg_vertices": [int(graph.vertex(1))],
                       "endpoints": [[int(graph.vertex(s)) for s in edge] for edge in edges],
                       "kappa": [[int(powers[0]) if powers else 0] for powers in kappa],
                       "leg_psi": [int(psi.get(1, 0))],
                       "half_psi": [[int(psi.get(s, 0)) for s in edge] for edge in edges]})
        raw_vectors.append(element.vector(1))
        automorphisms.append(int(graph.automorphism_number()))
    require(matrix(QQ, raw_vectors) == matrix.identity(QQ, 3), "Column meaning or order changed")
    require(automorphisms == [1, 1, 2], "Raw graph automorphisms changed")
    parameters = relations.FZ_param_list(1, (1,))
    original = matrix(QQ, [[relations.FZ_coeff(i, p, 1, 1, (1,), MODULI_ST)
                           for i in range(3)] for p in parameters])
    require(original == relations.FZ_matrix(1, 1, (1,), MODULI_ST),
            "Generator provenance no longer covers the complete source matrix")
    rows = matrix(QQ, [algebra.convert_vector_to_monomial_basis(row, 1, 1, (1,), MODULI_ST)
                       for row in original.rows()])
    requested = (classes[1] - QQ(1) / 24 * classes[2]).vector(1)
    witness = rows.solve_left(requested)
    require(witness * rows == requested, "Exact row witness failed")
    require(requested == vector(QQ, [0, 1, -QQ(1) / 24]), "Held request changed")
    rational = lambda q: [int(QQ(q).numerator()), int(QQ(q).denominator())]
    params = [{"sigma": [int(s) for s in p[0]],
               "marking_groups": [[int(label), [int(a) for a in powers]]
                                   for label, powers in p[1]]} for p in parameters]
    return {
        "schema_version": 1, "frame": FRAME, "locus": "full_stable",
        "genus": 1, "markings": [0], "codimension": 1,
        "normalization": "raw_gluing_pushforward", "source_label_map": [[1, 0]],
        "relation_source": RELATION_SOURCE, "generator_parameters": params,
        "graphs": graphs, "column_factors": [[1, 1]] * 3,
        "automorphism_counts": automorphisms,
        "rows": [[rational(q) for q in row] for row in rows],
        "requested": [rational(q) for q in requested],
        "witness": [rational(q) for q in witness],
        "environment": {"sage": version, "admcycles": "1.4",
                        "python": platform.python_version(), "architecture": platform.machine()},
        "producer_source_sha256": {Path(m.__file__).name:
            hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
            for m in (admcycles, stable_graph, tautological_ring, algebra, relations)},
        "exploration": {"online_lookup": False, "cache_ephemeral": True,
                        "original_rows": [[rational(q) for q in row] for row in original],
                        "raw_column_vectors": [[rational(q) for q in row] for row in raw_vectors],
                        "integrals": [rational(c.evaluate()) for c in classes]},
        "scope": "Candidate graphs and exact witness with original 3-spin generator parameters. "
                 "Geometric row vanishing remains an explicit class-level input; "
                 "no GW reconstruction equation or numerical seed is assumed.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-genus-one-psi-") as temporary:
        for variable, name in (("DOT_SAGE", "sage"), ("ADMCYCLES_CACHE_DIR", "admcycles"),
                               ("MPLCONFIGDIR", "matplotlib"), ("XDG_CACHE_HOME", "xdg")):
            location = Path(temporary) / name
            location.mkdir()
            os.environ[variable] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        result = json.dumps(run_search(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(result)
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
