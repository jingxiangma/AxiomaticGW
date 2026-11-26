#!/usr/bin/env python3
"""Search the full-stable marked genus-two codimension-two rows and emit their Lean certificate."""

import argparse
import importlib.metadata
import json
import os
from pathlib import Path
import tempfile

from export_admcycles_hodge_certificate import (
    INPUT_SHA256, REPOSITORY, dependencies, digest, graph_key, require, validate_packet,
)

DEFAULT = REPOSITORY / "AxiomaticGW/GKM/Fixtures/HodgeBoundarySquareRows.lean"


def search():
    from sage.all import QQ, identity_matrix, matrix
    from sage.version import version
    from admcycles import StableGraph, TautologicalRing, admcycles, stable_graph, tautological_ring
    from admcycles.DR import algebra, relations
    from admcycles.DR.moduli import MODULI_ST

    require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
            "Review the pinned Sage and admcycles versions")
    pins = json.loads((REPOSITORY / "environments/genus-one-psi-exploration.json").read_text())
    for module in (admcycles, algebra, relations, stable_graph, tautological_ring):
        path = Path(module.__file__)
        require(digest(path) == pins["producer_source_sha256"][path.name],
                f"Review the source pin for {path.name}")
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices, admcycles.genstobasis,
                                          admcycles.FZ_conjecture_holds)), "Online lookup active")
    shared, source = dependencies()
    path = REPOSITORY / "environments/admcycles-hodge-strata-candidates.json"
    require(digest(path) == INPUT_SHA256, "Held packet changed")
    packet = json.loads(path.read_text())
    validate_packet(packet, shared, source)
    ids = {}
    pairs = {}
    for pair in packet["pairs"]:
        pairs[tuple(pair["lambda_indices"])] = pair
        for component in pair["components"]:
            for term in component["terms"]:
                ids.setdefault(graph_key(term["graph"]), len(ids))

    ring = TautologicalRing(2, 1, moduli="st", base_ring=QQ)
    basis = list(identity_matrix(QQ, 17).rows())
    source_columns = []
    for i, v in enumerate(basis):
        element = ring.from_vector(v, 2)
        require(element.vector(2) == v, "Raw generator indexing changed")
        encoded, _ = source.encode_class(element, 2, QQ, shared.rational)
        terms = encoded[2]["terms"]
        require(len(terms) == 1 and terms[0]["coefficient"] == [1, 1], "Nonunit raw column")
        key = graph_key(terms[0]["graph"])
        if i == 0:
            require(ring.kappa(2).vector(2) == v and key not in ids,
                    "The auxiliary unmarked-decoration column must be kappa_2")
            source_columns.append("TautologicalStratum.kappaGenerator 2 (Fin 1) "
                                  "HodgeDegreeOneRealization.stable 2")
        else:
            require(key in ids, "Original raw column differs from the held generator's graph")
            source_columns.append(f"rawGraph{ids[key]}")

    def occurrences(class_element, pair):
        components, _ = source.encode_class(class_element, 2, QQ, shared.rational)
        require(components == pairs[pair]["components"], "Held graph occurrences changed")
        positions = {}
        for term in class_element._terms.values():
            for (kappa, psi), coefficient in zip(term.poly.monom, term.poly.coeff):
                if not coefficient:
                    continue
                key = graph_key(source.graph_packet(term.gamma, kappa, psi))
                v = ring(term.gamma, kappa=kappa, psi=psi).vector(2)
                require(v in basis, "A single raw decoration must give exactly one unit column")
                positions[key] = basis.index(v)
        return [positions[graph_key(t["graph"])] for t in components[2]["terms"]]

    lam1 = ring.lambdaclass(1, pull=True)
    lam2 = ring.lambdaclass(2, pull=True)
    half_indices = occurrences(lam2, (0, 2))
    square_indices = occurrences(lam1**2, (1, 1))
    require((len(half_indices), len(square_indices)) == (16, 28), "Held occurrence counts changed")
    sep = ring(StableGraph([1, 1], [[1, 2], [3]], [(2, 3)]))
    loop = ring(StableGraph([1], [[1, 2, 3]], [(2, 3)]))
    b2 = ((loop / 2 + 2 * sep)**2).vector(2)

    args = (2, 2, (1,), MODULI_ST)
    interior = relations.interior_FZ(*args)
    boundary = relations.boundary_FZ(*args)
    original = relations.FZ_matrix(*args)
    require(matrix(QQ, list(interior) + list(boundary)) == original,
            "Original interior and boundary generators changed")
    rows = matrix(QQ, [algebra.convert_vector_to_monomial_basis(v, *args) for v in original.rows()])
    require((rows.nrows(), rows.ncols()) == (14, 17), "Original row frame changed")
    residual = 200 * lam2.vector(2) - b2
    witness = rows.solve_left(residual)
    require(witness * rows == residual, "The requested class failed exact original-row replay")
    return {"columns": source_columns, "half_indices": half_indices, "square_indices": square_indices,
            "rows": list(rows.rows()), "lambda2": lam2.vector(2), "boundary_square": b2,
            "residual": residual, "witness": witness, "interior": len(interior),
            "boundary": len(boundary)}


def vec(items):
    lines = ["!["]
    for index, item in enumerate(map(str, items)):
        if index and len(lines[-1]) + len(item) + 3 > 86:
            lines[-1] += ","
            lines.append("      " + item)
        else:
            lines[-1] += (", " if index else "") + item
    return "\n".join(lines) + "]"


def lean_number(q):
    return str(q) if q.denominator() == 1 else f"({q.numerator()} / {q.denominator()})"


def rational_vec(v):
    return vec(map(lean_number, v))


def render(data):
    columns = "![\n    " + ",\n    ".join(data["columns"]) + "]"
    rows = "![\n    " + ",\n    ".join(rational_vec(row) for row in data["rows"]) + "]"
    return f'''/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeOneRealization

/-!
# Full-stable PPZ rows for the one-marked genus-two boundary square

Generated by `scripts/export_gkm_hodge_boundary_square.py` using Sage 10.9 and admcycles 1.4.
The original {data["interior"]} interior and {data["boundary"]} boundary generators appear in source order.
The seventeen columns use monomial kappa and raw gluing pushforwards throughout.
-/

@[expose] public section
namespace AxiomaticGW.GKM.HodgeBoundarySquareRows
open RelationCertificate AdmcyclesHodgeStrataCandidates

/-- The external graph order. The sole auxiliary column is the decorated kappa-two corolla. -/
noncomputable def columns : Fin 17 → TautologicalStratum 2 (Fin 1) :=
  {columns}

/-- Positions of the actual sixteen occurrences of the (0,2) packet. -/
def halfIndices : Fin 16 → Fin 17 :=
  {vec(data["half_indices"])}

/-- Positions of the actual twenty-eight occurrences of the (1,1) packet. -/
def squareIndices : Fin 28 → Fin 17 :=
  {vec(data["square_indices"])}

/-- Original full-stable PPZ generators in monomial coordinates. -/
def rows : Fin 14 → Coordinates 17 :=
  {rows}

/-- The complete source (0,2) graph polynomial. -/
def half : Coordinates 17 :=
  {rational_vec(data["lambda2"])}

/-- The source product of the discriminant boundary with itself, retaining shared edges. -/
def boundarySquare : Coordinates 17 :=
  {rational_vec(data["boundary_square"])}

/-- Difference of two hundred copies of the (0,2) packet and the discriminant square. -/
def residual : Coordinates 17 :=
  {rational_vec(data["residual"])}

/-- Exact witness using the full original row list. -/
def witness : Certificate 14 := ⟨
  {rational_vec(data["witness"])}⟩

/-- Arithmetic replay of the original-row expression in every source coordinate. -/
theorem checked : check rows residual witness = true := by decide +kernel

end AxiomaticGW.GKM.HodgeBoundarySquareRows
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="gkm-hodge-square-") as temporary:
        for variable in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            location = Path(temporary) / variable
            location.mkdir()
            os.environ[variable] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        output = render(search())
    if args.check:
        require(args.output.read_text() == output, "Held Lean rows differ from the original search")
        print("Matched 14 full-stable rows, 17 columns and both held packets.")
    else:
        args.output.write_text(output)


if __name__ == "__main__":
    main()
