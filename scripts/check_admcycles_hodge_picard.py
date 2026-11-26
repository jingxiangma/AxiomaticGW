#!/usr/bin/env python3
"""Check the original genus-two Picard row and its residual on the held Hodge packet."""

import importlib.metadata
import json
import os
from pathlib import Path
import tempfile

from export_admcycles_hodge_certificate import (
    INPUT_SHA256, REPOSITORY, dependencies, digest, require, validate_packet,
)


def check():
    from sage.all import QQ, matrix, vector
    from sage.version import version
    from admcycles import StableGraph, TautologicalRing, admcycles, stable_graph, tautological_ring
    from admcycles.DR import algebra, relations
    from admcycles.DR.moduli import MODULI_ST

    require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
            "Review the Sage/admcycles pin")
    original_pins = json.loads(
        (REPOSITORY / "environments/genus-one-psi-exploration.json").read_text()
    )["producer_source_sha256"]
    for source in (admcycles, algebra, relations, stable_graph, tautological_ring):
        path = Path(source.__file__)
        require(digest(path) == original_pins[path.name], f"Review the source pin for {path.name}")
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices, admcycles.genstobasis,
                                          admcycles.FZ_conjecture_holds)), "Online lookup active")

    path = REPOSITORY / "environments/admcycles-hodge-strata-candidates.json"
    require(digest(path) == INPUT_SHA256, "Held Hodge packet changed")
    shared, source = dependencies()
    packet = json.loads(path.read_text())
    validate_packet(packet, shared, source)
    ring = TautologicalRing(2, 1, moduli="st", base_ring=QQ)
    lam = ring.lambdaclass(1, pull=True)
    held = next(pair for pair in packet["pairs"] if pair["lambda_indices"] == [0, 1])
    components, _ = source.encode_class(lam, 1, QQ, shared.rational)
    require(components == held["components"], "The held degree-one graph terms changed")

    sep_graph = StableGraph([1, 1], [[1, 2], [3]], [(2, 3)])
    loop_graph = StableGraph([1], [[1, 2, 3]], [(2, 3)])
    sep, loop = ring(sep_graph), ring(loop_graph)
    columns = [ring.kappa(1), ring.psi(1), sep, loop]
    require(matrix(QQ, [a.vector(1) for a in columns]) == matrix.identity(QQ, 4),
            "Original graph frame or raw pushforward normalization changed")
    require((sep_graph.automorphism_number(), loop_graph.automorphism_number()) == (1, 2),
            "The marked separating graph or loop symmetry changed")

    parameters = relations.FZ_param_list(0, (1,))
    require(parameters == [((), ((1, (0,)),))], "Original generator parameters changed")
    generators = matrix(QQ, [[relations.FZ_coeff(i, p, 2, 1, (1,), MODULI_ST)
                              for i in range(4)] for p in parameters])
    require(generators == relations.FZ_matrix(2, 1, (1,), MODULI_ST),
            "The full-stable original FZ generator differs from its parameters")
    rows = matrix(QQ, [algebra.convert_vector_to_monomial_basis(row, 2, 1, (1,), MODULI_ST)
                       for row in generators.rows()])
    require(rows == matrix(QQ, [[-30, 30, 42, 3]]), "Original monomial 3-spin row changed")
    boundary = loop / 2 + 2 * sep
    residual = (10 * lam - boundary).vector(1)
    witness = rows.solve_left(residual)
    require(witness == vector(QQ, [-QQ(1) / 36]) and witness * rows == residual,
            "The original row does not certify the requested marked discriminant residual")
    return {"genus": 2, "markings": 1, "codimension": 1, "full_stable": True,
            "raw_frame": ["kappa_1", "psi_1", "separating", "loop"],
            "row": [int(value) for value in rows[0]], "witness": str(witness[0]),
            "ten_lambda_minus_boundary": [str(q) for q in residual],
            "held_graph_occurrences": len(components[1]["terms"]),
            "held_packet_sha256": INPUT_SHA256}



def check_second_chern():
    from sage.all import QQ, matrix, vector
    from export_gkm_hodge_boundary_square import search

    frame = search()
    # The Lean graph isomorphisms identify the ordered loops and both mixed refinements.
    coefficients = {"rawGraph12": 1, "rawGraph18": 4, "rawGraph19": 4}
    require(all(frame["columns"].count(graph) == 1 for graph in coefficients),
            "A normalization graph is missing from the original degree-two frame")
    refinement = vector(QQ, [coefficients.get(graph, 0) for graph in frame["columns"]])
    residual = 960 * frame["lambda2"] - refinement
    generators = matrix(QQ, frame["rows"])
    multipliers = generators.solve_left(residual)
    expected = ["4/27", "-1/2592", "5/7776", "-2/3", "1/972", "-1/324", "-4/27",
                "10/27", "0", "20/27", "-20/27", "2/27", "0", "0"]
    require(multipliers == vector(QQ, expected) and multipliers * generators == residual,
            "The original PPZ generators failed the requested second-Chern normalization")
    return {"source_columns": 17, "refinement_coefficients": coefficients,
            "multipliers": [str(q) for q in multipliers]}


def main():
    with tempfile.TemporaryDirectory(prefix="gkm-hodge-picard-") as temporary:
        for variable in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            location = Path(temporary) / variable
            location.mkdir()
            os.environ[variable] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        picard = check()
        picard["second_chern_normalization"] = check_second_chern()
        print(json.dumps(picard, indent=2))


if __name__ == "__main__":
    main()
