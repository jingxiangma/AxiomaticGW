#!/usr/bin/env python3
"""Search the two-marked genus-two cotangent-product relation.

The complete kappa-free boundary is retained. Its genus-two term has one
component marking; it is not a lower-genus term. Original 3-spin validity
and primitive gluing compatibility remain geometric inputs to Lean replay.
"""
import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import sys
import tempfile

sys.dont_write_bytecode = True
from export_admcycles_certificate import require

FRAME = "genus_two_psi_product_mbar_2_2_v1"
RELATION_SOURCE = "arXiv:1303.1043; admcycles 1.4 original full-stable 3-spin rows"
SELECTED = list(range(12)) + [13]


def run_search():
    from sage.all import QQ, identity_matrix, matrix, vector
    from sage.version import version
    from admcycles import TautologicalRing, admcycles, stable_graph, tautological_ring
    from admcycles.DR import algebra, graph as dr_graph, relations
    from admcycles.DR.moduli import MODULI_ST
    require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
            "Review the environment pin")
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices,
            admcycles.genstobasis, admcycles.FZ_conjecture_holds)), "Online lookup active")
    rational = lambda x: [int(QQ(x).numerator()), int(QQ(x).denominator())]
    vec = lambda row: [rational(x) for x in row]
    mat = lambda rows: [vec(row) for row in rows]
    parameter = lambda p: {"sigma": [int(x) for x in p[0]],
        "marking_groups": [[int(label), list(map(int, powers))] for label, powers in p[1]]}
    ring = TautologicalRing(2, 2, moduli="st", base_ring=QQ)
    classes = ring.generators(2)
    require(len(classes) == 38, "Changed target frame")
    graphs, raw, autos = [], [], []
    for index, element in enumerate(classes):
        require(len(element._terms) == 1, "Expected one raw graph")
        term = next(iter(element._terms.values()))
        require(list(term.poly.coeff) == [1] and len(term.poly.monom) == 1,
                "Expected a unit monomial coefficient")
        kappa, psi = term.poly.monom[0]
        G = term.gamma
        require(all(len(p) <= 2 for p in kappa), "Unexpected kappa degree")
        graphs.append({"index": index, "genus": list(map(int, G.genera())),
            "leg_vertices": [int(G.vertex(l)) for l in (1, 2)],
            "endpoints": [[int(G.vertex(h)) for h in ed] for ed in G.edges()],
            "kappa": [[int(p[j]) if j < len(p) else 0 for j in range(2)] for p in kappa],
            "leg_psi": [int(psi.get(l, 0)) for l in (1, 2)],
            "half_psi": [[int(psi.get(h, 0)) for h in ed] for ed in G.edges()]})
        raw.append(element.vector(2))
        autos.append(int(dr_graph.autom_count(index, 2, 2, (1, 2), MODULI_ST)))
    require(matrix(QQ, raw) == identity_matrix(QQ, 38), "Changed raw coordinates")
    params = relations.FZ_param_list(3, (1, 2))
    require(len(params) == 10, "Changed interior parameters")
    full = relations.FZ_matrix(2, 2, (1, 2), MODULI_ST)
    require(full.dimensions() == (27, 38), "Changed full generator matrix")
    original, provenance = [], []
    for i, p in enumerate(params):
        row = vector(QQ, [relations.FZ_coeff(j, p, 2, 2, (1, 2), MODULI_ST)
                          for j in range(38)])
        require(row == full[i], "Interior provenance differs")
        original.append(row)
        provenance.append({"kind": "interior", "upstream_index": i, "parameter": parameter(p)})
    count = 10
    for base_index, G in enumerate(dr_graph.all_strata(2, 1, (1, 2), MODULI_ST)):
        for orbit in relations.graph_count_automorphisms(G, True):
            v = orbit[0]
            if any(relations.R(G.M[v, j][0]) != G.M[v, j] for j in range(G.M.ncols())):
                continue
            g, n = int(G.M[v, 0][0]), int(G.degree(v))
            if 3 < g + 1 or relations.dim_form(g, n, MODULI_ST) < 1:
                continue
            for p in relations.reduced_FZ_param_list(G, v, g, n, 2 - g):
                if count in SELECTED:
                    sources = dr_graph.all_strata(g, 1, tuple(range(1, n + 1)), MODULI_ST)
                    destinations = []
                    for source in sources:
                        H = dr_graph.Graph(G.M)
                        H.replace_vertex_with_graph(v, source)
                        destinations.append(int(dr_graph.num_of_stratum(H, 2, 2, (1, 2), MODULI_ST)))
                    require(all(i >= 0 for i in destinations), "Dropped source column")
                    coefficients = [relations.FZ_coeff(j, p, g, 1, tuple(range(1, n + 1)),
                                                       MODULI_ST) for j in range(len(sources))]
                    row = vector(QQ, 38)
                    for j, c in zip(destinations, coefficients):
                        row[j] += c
                    require(row == full[count], "Boundary provenance differs")
                    original.append(row)
                    provenance.append({"kind": "separating", "upstream_index": count,
                        "base_index": base_index, "vertex_one_based": int(v),
                        "source_genus": g, "source_arity": n, "source_codimension": 1,
                        "parameter": parameter(p), "destinations": destinations,
                        "coefficients": vec(coefficients)})
                count += 1
    require(count == 27 and len(original) == 13, "Incomplete source enumeration")
    forward = matrix(QQ, [algebra.convert_vector_to_monomial_basis(e, 2, 2, (1, 2), MODULI_ST)
                         for e in identity_matrix(QQ, 38)])
    inverse = matrix(QQ, [algebra.convert_vector_to_pushforward_basis(e, 2, 2, (1, 2), MODULI_ST)
                         for e in identity_matrix(QQ, 38)])
    expected = identity_matrix(QQ, 38)
    expected[1, 0] = 1
    require(forward == expected and forward * inverse == identity_matrix(QQ, 38),
            "Kappa conversion changed")
    rows = matrix(QQ, original) * forward
    target = (ring.psi(1) * ring.psi(2)).vector(2)
    require(target == identity_matrix(QQ, 38)[5], "Changed cotangent product")
    forbidden = [i for i, g in enumerate(graphs)
                 if not g["endpoints"] or any(any(k) for k in g["kappa"])]
    witness = rows.matrix_from_columns(forbidden).solve_left(vector(QQ, [target[i] for i in forbidden]))
    requested = witness * rows
    boundary = target - requested
    require(all(boundary[i] == 0 for i in forbidden), "Failed complete elimination")
    require([i for i, c in enumerate(boundary) if c and 2 in graphs[i]["genus"]] == [8]
            and boundary[8] == 3, "Changed same-genus remainder")
    relation = ring.from_vector(requested, 2)
    diagnostics = [(relation * ring.psi(1)**a * ring.psi(2)**(3-a)).evaluate() for a in range(4)]
    require(all(x == 0 for x in diagnostics), "Intersection diagnostic failed")
    return {"schema_version": 1, "frame": FRAME, "locus": "full_stable", "genus": 2,
        "markings": [0, 1], "codimension": 2, "normalization": "raw_gluing_pushforward",
        "source_label_map": [[1, 0], [2, 1]], "relation_source": RELATION_SOURCE,
        "generator_provenance": provenance, "graphs": graphs, "column_factors": [[1, 1]]*38,
        "automorphism_counts": autos, "original_rows": mat(original), "rows": mat(rows),
        "requested": vec(requested), "boundary": vec(boundary), "witness": vec(witness),
        "pushforward_to_monomial": mat(forward), "monomial_to_pushforward": mat(inverse),
        "environment": {"sage": version, "admcycles": "1.4", "python": platform.python_version(),
                        "architecture": platform.machine()},
        "producer_source_sha256": {Path(m.__file__).name: hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
            for m in (admcycles, stable_graph, tautological_ring, algebra, dr_graph, relations)},
        "exploration": {"online_lookup": False, "cache_ephemeral": True,
                        "intersection_tests": vec(diagnostics)},
        "scope": "Exact two-marked cotangent product minus its full kappa-free boundary. "
            "Geometric source validity remains explicit. The genus-two remainder has one "
            "component marking; no numerical invariant or complete reconstruction is certified."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-psi-product-") as tmp:
        for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            p = Path(tmp) / name
            p.mkdir()
            os.environ[name] = str(p)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        result = run_search()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
