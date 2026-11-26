#!/usr/bin/env python3
"""Search a raw marked genus-two psi-square relation with source provenance.

Six original full-stable 3-spin rows are combined with one explicit gluing
of the original genus-one kappa/psi/loop row. Geometric row validity remains
an input; exact arithmetic and intersection diagnostics do not prove it.
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

FRAME = "genus_two_psi_square_mbar_2_1_v1"
RELATION_SOURCE = "arXiv:1303.1043; admcycles 1.4 original full-stable 3-spin rows and explicit elliptic gluing"


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
    genus, degree, marks = 2, 2, (1,)
    ring = TautologicalRing(genus, len(marks), moduli="st", base_ring=QQ)
    classes = ring.generators(degree)
    require(len(classes) == 17, "Changed marked frame size")
    graphs, raw_vectors, automorphisms, pure_automorphisms = [], [], [], []
    for index, element in enumerate(classes):
        require(len(element._terms) == 1, "Expected one raw graph term")
        term = next(iter(element._terms.values()))
        require(list(term.poly.coeff) == [1] and len(term.poly.monom) == 1,
                "Expected a unit monomial coefficient")
        kappa, psi = term.poly.monom[0]
        graph = term.gamma
        require(all(len(powers) <= degree for powers in kappa), "Unexpected kappa degree")
        edges = graph.edges()
        graphs.append({"index": index, "genus": [int(g) for g in graph.genera()],
                       "leg_vertices": [int(graph.vertex(1))],
                       "endpoints": [[int(graph.vertex(s)) for s in edge] for edge in edges],
                       "kappa": [[int(powers[i]) if i < len(powers) else 0
                                  for i in range(degree)] for powers in kappa],
                       "leg_psi": [int(psi.get(1, 0))],
                       "half_psi": [[int(psi.get(s, 0)) for s in edge] for edge in edges]})
        raw_vectors.append(element.vector(degree))
        # Decorations can break branch symmetries; the pure graph order is insufficient.
        automorphisms.append(int(dr_graph.autom_count(index, genus, degree, marks, MODULI_ST)))
        pure_automorphisms.append(int(graph.automorphism_number()))
    require(matrix(QQ, raw_vectors) == identity_matrix(QQ, 17), "Changed raw columns")
    parameters = relations.FZ_param_list(3 * degree - genus - 1, marks)
    interior = matrix(QQ, [[relations.FZ_coeff(i, p, genus, degree, marks, MODULI_ST)
                           for i in range(17)] for p in parameters])
    require(interior == matrix(QQ, relations.interior_FZ(genus, degree, marks, MODULI_ST)),
            "Original generator provenance differs from interior rows")
    require(interior.nrows() == 6, "Changed original row count")

    # Glue the unmarked elliptic factor of the unique separating boundary.
    # Retain the actual source graph replacement map, not only its resulting vector.
    boundary_graph = dr_graph.all_strata(2, 1, marks, MODULI_ST)[2]
    require(boundary_graph.num_vertices() == 2 and boundary_graph.M[1, 0] == 1
            and boundary_graph.degree(1) == 1, "Changed gluing source")
    source_strata = dr_graph.all_strata(1, 1, (1,), MODULI_ST)
    targets = []
    for source in source_strata:
        glued = dr_graph.Graph(boundary_graph.M)
        glued.replace_vertex_with_graph(1, source)
        targets.append(int(dr_graph.num_of_stratum(glued, genus, degree, marks, MODULI_ST)))
    require(targets == [8, 9, 14], "Changed elliptic boundary column map")
    source_parameter = ((1,), ((1, (0,)),))
    source_row = vector(QQ, [relations.FZ_coeff(i, source_parameter, 1, 1, (1,), MODULI_ST)
                             for i in range(len(source_strata))])
    require(source_row == vector(QQ, [102, -30, -3]), "Changed original elliptic row")
    glued_row = vector(QQ, 17)
    for i, destination in enumerate(targets):
        glued_row[destination] += source_row[i]
    original = matrix(QQ, list(interior.rows()) + [glued_row])
    require(original == relations.FZ_matrix(genus, degree, marks, MODULI_ST)[:7],
            "Explicit source rows differ from the upstream prefix")
    to_monomial = matrix(QQ, [algebra.convert_vector_to_monomial_basis(e, genus, degree,
        marks, MODULI_ST) for e in identity_matrix(QQ, 17).rows()])
    to_pushforward = matrix(QQ, [algebra.convert_vector_to_pushforward_basis(e, genus, degree,
        marks, MODULI_ST) for e in identity_matrix(QQ, 17).rows()])
    require(to_monomial * to_pushforward == identity_matrix(QQ, 17) and
            to_pushforward * to_monomial == identity_matrix(QQ, 17), "Kappa inverse failed")
    rows = original * to_monomial
    psi_square = (ring.psi(1) ** 2).vector(degree)
    require(psi_square == identity_matrix(QQ, 17).row(3), "Changed psi-square column")
    forbidden = [i for i, g in enumerate(graphs)
                 if not g["endpoints"] or any(any(p) for p in g["kappa"])]
    witness = rows.matrix_from_columns(forbidden).solve_left(
        vector(QQ, [psi_square[i] for i in forbidden]))
    requested = witness * rows
    boundary = psi_square - requested
    require(all(boundary[i] == 0 for i in forbidden), "Failed boundary/kappa elimination")
    require(all(max(graphs[i]["genus"]) < 2 for i in range(17) if boundary[i]),
            "Remainder did not lower vertex genus")
    relation_class = ring.from_vector(requested, degree)
    diagnostics = [(relation_class * c).evaluate() for c in classes]
    require(all(v == 0 for v in diagnostics), "Intersection diagnostic failed")
    rational = lambda q: [int(QQ(q).numerator()), int(QQ(q).denominator())]
    vec = lambda row: [rational(q) for q in row]
    mat = lambda a: [vec(row) for row in a.rows()]
    params = [{"sigma": [int(s) for s in p[0]],
               "marking_groups": [[int(label), [int(a) for a in powers]]
                                  for label, powers in p[1]]} for p in parameters]
    return {"schema_version": 1, "frame": FRAME, "locus": "full_stable", "genus": genus,
            "markings": [0], "codimension": degree, "normalization": "raw_gluing_pushforward",
            "source_label_map": [[1, 0]], "relation_source": RELATION_SOURCE,
            "generator_parameters": params, "graphs": graphs,
            "column_factors": [[1, 1]] * 17, "automorphism_counts": automorphisms,
            "rows": mat(rows), "requested": vec(requested), "boundary": vec(boundary),
            "witness": vec(witness), "original_rows": mat(original),
            "pushforward_to_monomial": mat(to_monomial),
            "monomial_to_pushforward": mat(to_pushforward),
            "gluing_provenance": {"source_genus": 1, "source_markings": [1],
                "source_codimension": 1, "sigma": [1], "marking_groups": [[1, [0]]],
                "source_row": vec(source_row), "boundary_stratum_index": 2,
                "replaced_vertex_one_based": 1, "target_columns": targets},
            "environment": {"sage": version, "admcycles": "1.4",
                "python": platform.python_version(), "architecture": platform.machine()},
            "producer_source_sha256": {Path(m.__file__).name:
                hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
                for m in (admcycles, stable_graph, tautological_ring, algebra, dr_graph, relations)},
            "exploration": {"online_lookup": False, "cache_ephemeral": True,
                "raw_column_vectors": mat(matrix(QQ, raw_vectors)),
                "pure_graph_automorphisms": pure_automorphisms,
                "intersection_tests": [rational(v) for v in diagnostics],
                "psi_four_integral": rational((ring.psi(1) ** 4).evaluate())},
            "scope": "Candidate marked psi-square relation from six original 3-spin rows and "
                "one explicitly pushed elliptic row. Geometric row vanishing and compatibility "
                "of the gluing operation remain class-level obligations. No genus-two GW value "
                "or descendant reconstruction is assumed or certified by this search."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-genus-two-psi-square-") as directory:
        for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            location = Path(directory) / name
            location.mkdir()
            os.environ[name] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        result = run_search()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
