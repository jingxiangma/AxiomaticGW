#!/usr/bin/env python3
"""Export marked candidate graphs and exact replay against the fixed WDVV frame.

Ordinary Python and Lean suffice; Sage is used only for prior exploration.
Incoming incidence and decoration data are emitted, not replaced by the
trusted columns. Lean proves each semantic column equality before accepting
the original rows, normalization, held request, and row witness.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys

from export_admcycles_certificate import (
    integer, rational_matrix, rational_vector, require, unique_object, vector,
)


FRAME = "wdvv_mbar_0_4_v1"
RELATION_IDS = ["keel_01_23_minus_02_13", "keel_02_13_minus_03_12"]
RELATION_SOURCE = "10.1090/S0002-9947-1992-1034665-0; Section 4, Theorem 1, I(2)"


def naturals(values, length, message):
    require(isinstance(values, list) and len(values) == length, message)
    require(all(integer(q, message) >= 0 for q in values), message)
    return values


def decode_graph(graph, index):
    require(set(graph) == {"index", "genus", "leg_vertices", "endpoints", "kappa",
                           "leg_psi", "half_psi"}, "Unknown or missing graph field")
    require(integer(graph["index"], "Invalid graph index") == index, "Reordered graph slots")
    genera, edges = graph["genus"], graph["endpoints"]
    require(isinstance(genera, list) and 1 <= len(genera) <= 2, "Unsupported vertex count")
    require(isinstance(edges, list) and len(edges) <= 1, "Unsupported edge count")
    vertices, edge_count = len(genera), len(edges)
    naturals(genera, vertices, "Invalid vertex genus")
    legs = naturals(graph["leg_vertices"], 4, "Invalid external incidence")
    require(all(v < vertices for v in legs), "External vertex out of range")
    for edge in edges:
        naturals(edge, 2, "Invalid edge pair")
        require(all(v < vertices for v in edge), "Edge vertex out of range")
    kappa, half_psi = graph["kappa"], graph["half_psi"]
    require(isinstance(kappa, list) and len(kappa) == vertices, "Invalid kappa shape")
    require(isinstance(half_psi, list) and len(half_psi) == edge_count, "Invalid node shape")
    for row in kappa:
        naturals(row, 1, "Invalid kappa exponent")
    for row in half_psi:
        naturals(row, 2, "Invalid node psi power")
    naturals(graph["leg_psi"], 4, "Invalid external psi power")
    # Only shape and range checks occur here. Stability, connectedness, genus,
    # and equality to the fixed mathematical columns are kernel obligations.
    return graph


def graph_source(index, graph):
    name = f"incomingGraph{index}"
    v, e = len(graph["genus"]), len(graph["endpoints"])
    nested = lambda rows: vector([vector([str(x) for x in row]) for row in rows])
    return "\n".join([
        f"def {name}Candidate : StableGraphCode.Candidate (Fin 4) {v} {e} where",
        f"  legVertex := {vector([str(x) for x in graph['leg_vertices']])}",
        f"  endpoint := {nested(graph['endpoints'])}",
        f"  genus := {vector([str(x) for x in graph['genus']])}", "",
        f"theorem {name}Valid : {name}Candidate.Valid 0 := by decide", "",
        f"def {name}Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) {v} {e} 1 → ℕ",
        f"  | .inl (vertex, index) => ({nested(graph['kappa'])} : Fin {v} → Fin 1 → ℕ)",
        "      vertex index",
        f"  | .inr (.inl label) => ({vector([str(x) for x in graph['leg_psi']])}) label",
        (f"  | .inr (.inr (edge, branch)) => ({nested(graph['half_psi'])}) edge branch"
         if e else "  | .inr (.inr (edge, _)) => Fin.elim0 edge"), "",
        f"def {name} : TautologicalStratum 0 (Fin 4) :=",
        "  TautologicalStratum.mk",
        "    (DecoratedStableGraph.toDecoration",
        f"      {name}Candidate {name}Valid {name}Exponents)",
        "    (DecoratedStableGraph.toDecoration_totalGenus",
        f"      {name}Candidate {name}Valid {name}Exponents)", "",
        f"theorem {name}_eq : {name} = WDVV.columns {index} :=",
        "  TautologicalStratum.mk_eq_mk_of_isomorphic?",
        "    (DecoratedStableGraph.toDecoration_totalGenus",
        f"      {name}Candidate {name}Valid {name}Exponents)",
        f"    (WDVV.graph_totalGenus {index})",
        "    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)", "",
    ])


def replay_source(report, graphs, digest):
    rows = rational_matrix(report["rows"], 2, 3)
    for key, length in (("column_factors", 3), ("requested", 3), ("witness", 2)):
        require(isinstance(report[key], list) and len(report[key]) == length,
                f"Wrong {key} size")
    factors, request, witness = (rational_vector(report[key])
                                 for key in ("column_factors", "requested", "witness"))
    return "\n".join([
        "/- Candidate marked WDVV replay. Geometric boundary equality remains a hypothesis.",
        "Input SHA256:", f"{digest}", "This digest is provenance, not proof. -/",
        "module", "", "public import AxiomaticGW.Tautological.WDVVRealization", "",
        "public import AxiomaticGW.Tautological.GraphEnumeration", "",
        "@[expose] public section", "", "namespace AxiomaticGW.WDVVReplay", "",
        *[graph_source(i, graph) for i, graph in enumerate(graphs)],
        "def incomingColumns : Fin 3 → TautologicalStratum 0 (Fin 4) :=",
        "  ![incomingGraph0, incomingGraph1, incomingGraph2]", "",
        "def presentation : RelationCertificate.Presentation 0 (Fin 4) 2 3 where",
        "  columns := incomingColumns", f"  columnFactors := {factors}",
        f"  rows := {rows}", f"  claimedRequest := {request}",
        f"  certificate := ⟨{witness}⟩", "",
        "theorem accepted : WDVV.AcceptsExchange presentation := by",
        "  constructor", "  · refine ⟨?_, ?_, ?_, ?_⟩",
        "    · change incomingColumns = WDVV.columns",
        "      funext i", "      fin_cases i",
        *[f"      · exact incomingGraph{i}_eq" for i in range(3)],
        "    · funext i", "      fin_cases i <;> norm_num [presentation, Matrix.cons_val_two]",
        "    · rfl", "    · rfl",
        "  · funext i", "    fin_cases i <;>",
        "      norm_num [RelationCertificate.combination, presentation, WDVV.rows,",
        "        WDVV.requested, Fin.sum_univ_two, Matrix.cons_val_two]", "",
        "/-- Offline replay certifies the held formal consequence in the fixed row span. -/",
        "theorem requested_mem_relationSpan :",
        "    RelationCertificate.interpret WDVV.columns WDVV.requested ∈",
        "      RelationCertificate.relationSpan WDVV.columns WDVV.rows :=",
        "  RelationCertificate.acceptsPresentation_sound _ _ _ presentation accepted", "",
        "end AxiomaticGW.WDVVReplay", "",
    ])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    args = parser.parse_args()
    raw = args.report.read_bytes()
    report = json.loads(raw, object_pairs_hook=unique_object)
    require(integer(report["schema_version"], "Invalid schema version") == 1, "Wrong schema")
    require(report["frame"] == FRAME and report["locus"] == "full_stable", "Wrong frame/locus")
    require(integer(report["genus"], "Invalid genus") == 0 and
            integer(report["codimension"], "Invalid codimension") == 1, "Wrong genus/degree")
    require(naturals(report["markings"], 4, "Invalid markings") == [0, 1, 2, 3], "Wrong labels")
    require(report["normalization"] == "raw_gluing_pushforward", "Wrong normalization")
    label_map = report["source_label_map"]
    require(isinstance(label_map, list) and len(label_map) == 4, "Invalid label map shape")
    for pair in label_map:
        naturals(pair, 2, "Invalid label conversion integer")
    require(label_map == [[1, 0], [2, 1], [3, 2], [4, 3]], "Wrong label map")
    require(report["relation_ids"] == RELATION_IDS and
            report["relation_source"] == RELATION_SOURCE, "Wrong relation references")
    require(report["environment"]["sage"] == "10.9" and
            report["environment"]["admcycles"] == "1.4", "Wrong tool versions")
    require(isinstance(report["graphs"], list) and len(report["graphs"]) == 3,
            "Wrong graph count")
    graphs = [decode_graph(graph, i) for i, graph in enumerate(report["graphs"])]
    print(replay_source(report, graphs, hashlib.sha256(raw).hexdigest()), end="")


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"WDVV export failed: {error}", file=sys.stderr)
        sys.exit(1)
