#!/usr/bin/env python3
"""Emit candidate Lean replay data for the fixed unmarked genus-two fixture.

Input is the exact JSON produced by admcycles_smoke.py. The trusted graph
frame, relation rows, and requested expression live in AdmcyclesGenusTwo.lean;
this exporter cannot redefine them. It emits proposed graphs, rows, and row
weights plus kernel proof replay against that fixed request. Parsing and
Sage are outside the proof boundary. This first fixture does not certify the
geometric validity of the FZ rows or implement general GW reconstruction.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys


GRAPH_ENCODING = "admcycles.DR.Graph.M; sorted sparse [exponent_tuple, integer_coefficient]"
# This selects a faster kernel proof for identical coordinates. Both paths
# still prove equality to the compiled Lean frame; the digest proves nothing.
PINNED_RAW_COORDINATES_SHA256 = "fe39fa56cd4c02c313c92720196987d18d45376c7c00813e6d7d62ca9fd0b055"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, message):
    require(type(value) is int, message)
    return value


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def polynomial(entry):
    require(isinstance(entry, list), "Polynomial must be a sparse term list")
    result = {}
    for term in entry:
        require(isinstance(term, list) and len(term) == 2, "Invalid polynomial term")
        powers, coefficient = term
        require(isinstance(powers, list) and len(powers) == 1, "Expected one polynomial variable")
        power = integer(powers[0], "Polynomial power must be an integer")
        coefficient = integer(coefficient, "Polynomial coefficient must be an integer")
        require(power >= 0 and power not in result, "Negative or repeated polynomial power")
        require(coefficient != 0, "Sparse polynomial contains a zero coefficient")
        result[power] = coefficient
    return result


def decode_graph(graph, expected_index):
    """Decode only internal edges; loop X and X^2 coefficients are separate psi powers."""
    require(integer(graph["index"], "Graph index must be an integer") == expected_index,
            "Graph indices are missing or reordered")
    rows = integer(graph["rows"], "Row count must be an integer")
    columns = integer(graph["columns"], "Column count must be an integer")
    require(rows >= 2 and columns >= 1, "Empty vertex set or missing genus column")
    raw = graph["matrix_polynomials"]
    require(len(raw) == rows and all(len(row) == columns for row in raw), "Matrix shape mismatch")
    matrix = [[polynomial(entry) for entry in row] for row in raw]
    require(matrix[0][0] == {0: -1}, "Invalid graph header")
    require(all(not matrix[0][j] for j in range(1, columns)), "This fixed request has no external markings")
    genus, kappa = [], []
    for i in range(1, rows):
        p = matrix[i][0]
        require(all(value >= 0 for value in p.values()), "Negative genus or kappa exponent")
        require(all(power <= 2 for power in p), "Kappa index exceeds this codimension bound")
        genus.append(p.get(0, 0))
        kappa.append([p.get(1, 0), p.get(2, 0)])
    endpoints, half_psi = [], []
    for j in range(1, columns):
        incident = [(i - 1, matrix[i][j]) for i in range(1, rows) if matrix[i][j]]
        require(all(all(value >= 0 for value in p.values()) for _, p in incident), "Negative incidence or psi exponent")
        if len(incident) == 1 and incident[0][1].get(0, 0) == 2:
            vertex, p = incident[0]
            require(all(power <= 2 for power in p), "Unsupported loop polynomial")
            endpoints.append([vertex, vertex])
            half_psi.append([p.get(1, 0), p.get(2, 0)])
        else:
            require(len(incident) == 2 and all(p.get(0, 0) == 1 for _, p in incident), "Malformed internal edge")
            require(all(all(power <= 1 for power in p) for _, p in incident), "Unsupported non-loop polynomial")
            endpoints.append([vertex for vertex, _ in incident])
            half_psi.append([p.get(1, 0) for _, p in incident])
    vertices, edges = rows - 1, columns - 1
    valence = [sum(edge.count(v) for edge in endpoints) for v in range(vertices)]
    require(all(3 <= 2 * genus[v] + valence[v] for v in range(vertices)), "Unstable vertex")
    reached = {0}
    while True:
        enlarged = reached | {v for edge in endpoints if any(w in reached for w in edge) for v in edge}
        if enlarged == reached:
            break
        reached = enlarged
    require(len(reached) == vertices, "Disconnected graph")
    require(sum(genus) + edges + 1 - vertices == 2, "Incorrect arithmetic genus")
    degree = edges + sum(a + 2 * b for a, b in kappa) + sum(sum(p) for p in half_psi)
    require(degree == 2, "Incorrect stratum codimension")
    return {"vertices": vertices, "edges": edges, "genus": genus, "kappa": kappa,
            "endpoints": endpoints, "half_psi": half_psi}


def rational(pair):
    require(isinstance(pair, list) and len(pair) == 2, "Invalid rational encoding")
    numerator = integer(pair[0], "Rational numerator must be an integer")
    denominator = integer(pair[1], "Rational denominator must be an integer")
    require(denominator > 0, "Rational denominator must be positive")
    return Fraction(numerator, denominator)


def vector(values):
    return "![" + ", ".join(values) + "]" if values else "Fin.elim0"


def rational_text(value):
    return str(value.numerator) if value.denominator == 1 else f"({value.numerator} / {value.denominator})"


def rational_vector(values):
    return vector([rational_text(rational(q)) for q in values])


def rational_matrix(rows, height, width):
    require(isinstance(rows, list) and len(rows) == height, "Wrong relation row count")
    require(all(isinstance(row, list) and len(row) == width for row in rows), "Wrong relation column count")
    return "![" + ",\n    ".join(rational_vector(row) for row in rows) + "]"


def graph_definitions(graphs, prefix):
    lines = []
    for index, graph in enumerate(graphs):
        name = f"{prefix}{index}"
        v, e = graph["vertices"], graph["edges"]
        endpoints = vector([vector([str(i) for i in pair]) for pair in graph["endpoints"]])
        genera = vector([str(g) for g in graph["genus"]])
        kappa = vector([vector([str(p) for p in powers]) for powers in graph["kappa"]])
        half_psi = vector([vector([str(p) for p in powers]) for powers in graph["half_psi"]])
        lines.extend([
            f"def {name}Candidate : StableGraphCode.Candidate (Fin 0) {v} {e} where",
            "  legVertex := Fin.elim0",
            f"  endpoint := {endpoints}",
            f"  genus := {genera}",
            "",
            f"theorem {name}Valid : {name}Candidate.Valid 2 := by decide",
            "",
            f"def {name}Exponents : DecoratedStableGraph.DecorationIndex (Fin 0) {v} {e} 2 → ℕ",
            f"  | .inl (vertex, index) => ({kappa} : Fin {v} → Fin 2 → ℕ) vertex index",
            "  | .inr (.inl label) => Fin.elim0 label",
            (f"  | .inr (.inr (edge, branch)) => ({half_psi} : Fin {e} → Fin 2 → ℕ) edge branch" if e else
             "  | .inr (.inr (edge, _)) => Fin.elim0 edge"),
            "",
            f"def {name} : TautologicalStratum 2 (Fin 0) :=",
            "  TautologicalStratum.mk",
            "    (DecoratedStableGraph.toDecoration",
            f"      {name}Candidate {name}Valid {name}Exponents)",
            "    (DecoratedStableGraph.toDecoration_totalGenus",
            f"      {name}Candidate {name}Valid {name}Exponents)",
            "",
        ])
    return "\n".join(lines)


def graph_equality_definitions():
    """Propose separate finite isomorphism proofs against each fixed slot."""
    lines = []
    for index in range(8):
        source = f"incomingGraph{index}"
        target = f"AdmcyclesGenusTwo.graph{index}"
        lines.extend([
            f"theorem {source}_eq : {source} = {target} :=",
            "  TautologicalStratum.mk_eq_mk_of_isomorphic?",
            "    (DecoratedStableGraph.toDecoration_totalGenus",
            f"      {source}Candidate {source}Valid {source}Exponents)",
            "    (DecoratedStableGraph.toDecoration_totalGenus",
            f"      {target}Candidate {target}Valid",
            f"      {target}Exponents)",
            "    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)",
            "",
        ])
    return "\n".join(lines)


def read_report(path):
    report = json.loads(path.read_text(), object_pairs_hook=unique_object)
    require(integer(report["schema_version"], "Schema version must be an integer") == 1
            and report["status"] == "passed", "Unsupported or failed smoke report")
    environment = report["environment"]
    require(environment["sage"] == "10.9" and environment["admcycles"] == "1.4", "Unsupported environment pin")
    coordinates = report["coordinates"]
    require((coordinates["genus"], coordinates["markings"], coordinates["codimension"]) == (2, [], 2), "Report does not match the fixed requested frame")
    require(coordinates["locus"] == "full_stable" and coordinates["polynomial_variables"] == ["X"], "Wrong locus or polynomial variables")
    require(coordinates["graph_encoding"] == GRAPH_ENCODING, "Unsupported graph encoding")
    graphs = coordinates["graphs"]
    require(len(graphs) == 8, "The fixed frame has eight columns")
    decoded = [decode_graph(graph, index) for index, graph in enumerate(graphs)]
    arithmetic = report["arithmetic"]
    require(arithmetic["rational_encoding"] == "[numerator, positive denominator]", "Unsupported rational encoding")
    for key, value in (("raw_coordinate_sha256", coordinates), ("exact_arithmetic_sha256", arithmetic)):
        encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
        require(report[key] == hashlib.sha256(encoded).hexdigest(), f"Report digest mismatch: {key}")
    return report, decoded


def replay_source(report, graphs):
    arithmetic = report["arithmetic"]
    rows = rational_matrix(arithmetic["fz_rows_monomial"], 7, 8)
    source_rows = rational_matrix(arithmetic["fz_rows_pushforward"], 7, 8)
    to_monomial = rational_matrix(report["coordinates"]["pushforward_to_monomial"], 8, 8)
    to_source = rational_matrix(report["coordinates"]["monomial_to_pushforward"], 8, 8)
    target = arithmetic["target_monomial"]
    source_target = arithmetic["target_pushforward"]
    witness = arithmetic["row_combination_witness"]
    require(len(target) == len(source_target) == 8 and len(witness) == 7,
            "Wrong target or witness length")
    column_proof = ["    rfl"]
    graph_proofs = ""
    if report["raw_coordinate_sha256"] != PINNED_RAW_COORDINATES_SHA256:
        graph_proofs = graph_equality_definitions()
        column_proof = [
            "    change incomingColumns = AdmcyclesGenusTwo.columns",
            "    funext column",
            "    fin_cases column",
            *[f"    · exact incomingGraph{i}_eq" for i in range(8)],
        ]
    parts = [
        "/- Candidate data generated by scripts/export_admcycles_certificate.py.",
        "The accepted claim is fixed in AdmcyclesGenusTwo; geometric row validity remains an input. -/",
        "module",
        "",
        "public import AxiomaticGW.Tautological.Fixtures.AdmcyclesGenusTwo",
        "",
        "@[expose] public section",
        "",
        "namespace AxiomaticGW.AdmcyclesGenusTwoReplay",
        "",
        graph_definitions(graphs, "incomingGraph"),
        graph_proofs,
        "def incomingColumns : Fin 8 → TautologicalStratum 2 (Fin 0) :=",
        "  ![" + ", ".join(f"incomingGraph{i}" for i in range(4)) + ",",
        "    " + ", ".join(f"incomingGraph{i}" for i in range(4, 8)) + "]",
        "",
        "def presentation : RelationCertificate.Presentation 2 (Fin 0) 7 8 where",
        "  columns := incomingColumns",
        "  columnFactors := 1",
        f"  rows := {rows}",
        f"  claimedRequest := {rational_vector(target)}",
        f"  certificate := ⟨{rational_vector(witness)}⟩",
        "",
        "def incoming : AdmcyclesGenusTwo.Exchange where",
        "  presentation := presentation",
        f"  sourceRows := {source_rows}",
        f"  sourceToMonomial := {to_monomial}",
        f"  monomialToSource := {to_source}",
        f"  sourceRequest := {rational_vector(source_target)}",
        "",
        "/-- Kernel replay binds all incoming fields to the fixed requested formal claim. -/",
        "theorem accepted : AdmcyclesGenusTwo.AcceptsExchange incoming := by",
        "  rw [AdmcyclesGenusTwo.AcceptsExchange]",
        "  constructor",
        "  · exact ⟨rfl, rfl, rfl, rfl⟩",
        "  rw [RelationCertificate.AcceptsPresentation]",
        "  constructor",
        "  · refine ⟨?_, rfl, rfl, rfl⟩",
        *column_proof,
        "  · ext column",
        "    fin_cases column <;>",
        "      norm_num only [RelationCertificate.combination, incoming, presentation,",
        "        AdmcyclesGenusTwo.rows,",
        "        AdmcyclesGenusTwo.requested, Fin.sum_univ_succ, Fintype.sum_empty,",
        "        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,",
        "        Matrix.cons_val_succ, Matrix.cons_val_fin_one]",
        "",
        "/-- Formal span membership; this does not assert geometric vanishing. -/",
        "theorem requested_mem_span : RelationCertificate.interpret AdmcyclesGenusTwo.columns",
        "    AdmcyclesGenusTwo.requested ∈ RelationCertificate.relationSpan",
        "      AdmcyclesGenusTwo.columns AdmcyclesGenusTwo.rows :=",
        "  AdmcyclesGenusTwo.acceptsExchange_sound incoming accepted",
        "",
        "end AxiomaticGW.AdmcyclesGenusTwoReplay",
        "",
    ]
    return "\n".join(parts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path, help="Exact JSON produced by admcycles_smoke.py")
    args = parser.parse_args()
    report, graphs = read_report(args.report)
    print(replay_source(report, graphs), end="")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as error:
        print(f"admcycles certificate export FAILED: {error}", file=sys.stderr)
        raise SystemExit(1)
