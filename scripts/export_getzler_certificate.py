#!/usr/bin/env python3
"""Decode exact Getzler graphs and emit claim-bound offline Lean replay.

Shape checks occur in Python. Stability, genus, graph equality, orbit
normalization, the original row, held request, and witness are Lean obligations.
The geometric Getzler relation remains an explicit class-level hypothesis.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys

from export_admcycles_certificate import (
    integer, rational_matrix, rational_vector, require, unique_object, vector,
)
from export_wdvv_certificate import naturals


FRAME = "getzler_mbar_1_4_v1"
RELATION_SOURCE = "10.1090/S0894-0347-97-00246-4; Theorem 1.8"
NAMES = {"delta22", "delta23", "delta24", "delta34", "delta03", "delta04", "deltaBeta"}
FIELDS = {"schema_version", "frame", "locus", "genus", "markings", "codimension",
          "normalization", "source_label_map", "relation_ids", "relation_source", "graphs",
          "column_factors", "orbifold_factors", "stratum_ids", "rows", "requested", "witness",
          "environment", "producer_source_sha256", "exploration", "scope"}


def decode_graph(graph, index):
    require(isinstance(graph, dict) and set(graph) == {"index", "genus", "leg_vertices",
            "endpoints", "kappa", "leg_psi", "half_psi"}, "Unknown or missing graph field")
    require(integer(graph["index"], "Invalid graph index") == index, "Reordered graph slots")
    genera, edges = graph["genus"], graph["endpoints"]
    require(isinstance(genera, list) and 1 <= len(genera) <= 3, "Unsupported vertex count")
    require(isinstance(edges, list) and len(edges) <= 2, "Unsupported edge count")
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
        naturals(row, 2, "Invalid kappa exponent")
    for row in half_psi:
        naturals(row, 2, "Invalid node psi power")
    naturals(graph["leg_psi"], 4, "Invalid external psi power")
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
        f"theorem {name}Valid : {name}Candidate.Valid 1 := by decide", "",
        f"def {name}Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) {v} {e} 2 → ℕ",
        f"  | .inl (vertex, index) => ({nested(graph['kappa'])} : Fin {v} → Fin 2 → ℕ)",
        "      vertex index",
        f"  | .inr (.inl label) => ({vector([str(x) for x in graph['leg_psi']])}) label",
        (f"  | .inr (.inr (edge, branch)) => ({nested(graph['half_psi'])}) edge branch"
         if e else "  | .inr (.inr (edge, _)) => Fin.elim0 edge"), "",
        f"def {name} : TautologicalStratum 1 (Fin 4) :=",
        "  TautologicalStratum.mk",
        "    (DecoratedStableGraph.toDecoration",
        f"      {name}Candidate {name}Valid {name}Exponents)",
        "    (DecoratedStableGraph.toDecoration_totalGenus",
        f"      {name}Candidate {name}Valid {name}Exponents)", "",
        f"theorem {name}_eq : {name} = GetzlerGraphs.columns {index} :=",
        "  TautologicalStratum.mk_eq_mk_of_isomorphic?",
        "    (DecoratedStableGraph.toDecoration_totalGenus",
        f"      {name}Candidate {name}Valid {name}Exponents)",
        f"    (GetzlerGraphs.graph_totalGenus {index})",
        "    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)", "",
    ])


def wrapped_vector(values):
    return "![\n" + "\n".join("    " + value + ("," if i < len(values) - 1 else "]")
                                for i, value in enumerate(values))


def replay_source(report, graphs, digest):
    rows = rational_matrix(report["rows"], 1, 33)
    decoded = {}
    for key, length in (("column_factors", 33), ("orbifold_factors", 33),
                        ("requested", 33), ("witness", 1)):
        require(isinstance(report[key], list) and len(report[key]) == length,
                f"Wrong {key} size")
        decoded[key] = rational_vector(report[key])
    names = report["stratum_ids"]
    require(isinstance(names, list) and len(names) == 33 and all(n in NAMES for n in names),
            "Invalid named stratum slots")
    text = [
        "/- Candidate Getzler replay. Geometric relation validity remains a hypothesis.",
        "Input SHA256:", digest, "This digest is provenance, not proof. -/",
        "module", "", "public import AxiomaticGW.Tautological.GetzlerRealization", "",
        "@[expose] public section", "", "namespace AxiomaticGW.GetzlerReplay", "",
        *[graph_source(i, graph) for i, graph in enumerate(graphs)],
        "def incomingColumns : Fin 33 → TautologicalStratum 1 (Fin 4) :=",
        "  " + wrapped_vector([f"incomingGraph{i}" for i in range(33)]), "",
        "def incomingNames : Fin 33 → GetzlerStratum :=",
        "  " + wrapped_vector(["." + n for n in names]), "",
        "def incomingOrbifoldFactors : RelationCertificate.Coordinates 33 :=",
        "  " + decoded["orbifold_factors"], "",
        "theorem names_correct : incomingNames = GetzlerGraphs.kind := by",
        "  funext i", "  fin_cases i <;> decide", "",
        "theorem conversion_correct : incomingOrbifoldFactors = GetzlerGraphs.normalization := by",
        "  funext i", "  fin_cases i <;>",
        "    norm_num [incomingOrbifoldFactors, GetzlerGraphs.normalization,",
        "      Matrix.cons_val_two]", "",
        "def presentation : RelationCertificate.Presentation 1 (Fin 4) 1 33 where",
        "  columns := incomingColumns", "  columnFactors := " + decoded["column_factors"],
        "  rows := " + rows, "  claimedRequest := " + decoded["requested"],
        "  certificate := ⟨" + decoded["witness"] + "⟩", "",
        "theorem accepted : GetzlerGraphs.AcceptsExchange presentation := by",
        "  constructor", "  · refine ⟨?_, ?_, ?_, ?_⟩",
        "    · change incomingColumns = GetzlerGraphs.columns",
        "      funext i", "      fin_cases i",
        *[f"      · exact incomingGraph{i}_eq" for i in range(33)],
        "    · funext i", "      fin_cases i <;> norm_num [presentation, Matrix.cons_val_two]",
        "    · funext r i", "      fin_cases r", "      fin_cases i <;>",
        "        norm_num [presentation, GetzlerGraphs.rows, GetzlerGraphs.row,",
        "          GetzlerGraphs.kind, GetzlerGraphs.normalization, GetzlerStratum.coefficient,",
        "          Matrix.cons_val_two]",
        "    · funext i", "      fin_cases i <;>",
        "        norm_num [presentation, GetzlerGraphs.requested, GetzlerGraphs.kind,",
        "          GetzlerGraphs.normalization, Matrix.cons_val_two]",
        "  · funext i", "    fin_cases i <;>",
        "      norm_num [RelationCertificate.combination, presentation, GetzlerGraphs.rows,",
        "        GetzlerGraphs.row, GetzlerGraphs.kind, GetzlerGraphs.normalization,",
        "        GetzlerStratum.coefficient, GetzlerGraphs.requested, Fin.sum_univ_one,",
        "        Matrix.cons_val_two]", "",
        "/-- Offline replay certifies the held delta23 consequence in the fixed relation span. -/",
        "theorem requested_mem_relationSpan :",
        "    RelationCertificate.interpret GetzlerGraphs.columns GetzlerGraphs.requested ∈",
        "      RelationCertificate.relationSpan GetzlerGraphs.columns GetzlerGraphs.rows :=",
        "  RelationCertificate.acceptsPresentation_sound _ _ _ presentation accepted", "",
        "end AxiomaticGW.GetzlerReplay", "",
    ]
    # Tables are deliberately emitted rather than substituted with trusted constants.
    # Wrap only commas: Lean vector notation allows newlines between entries.
    output = "\n".join(text)
    return "\n".join(line.replace(", ", ",\n    ") if len(line) > 100 else line
                      for line in output.split("\n"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    args = parser.parse_args()
    raw = args.report.read_bytes()
    report = json.loads(raw, object_pairs_hook=unique_object)
    require(isinstance(report, dict) and set(report) == FIELDS, "Unknown or missing report field")
    require(integer(report["schema_version"], "Invalid schema version") == 1, "Wrong schema")
    require(report["frame"] == FRAME and report["locus"] == "full_stable", "Wrong frame/locus")
    require(integer(report["genus"], "Invalid genus") == 1 and
            integer(report["codimension"], "Invalid codimension") == 2, "Wrong genus/degree")
    require(naturals(report["markings"], 4, "Invalid markings") == [0, 1, 2, 3], "Wrong labels")
    require(report["normalization"] == "raw_gluing_pushforward", "Wrong normalization")
    label_map = report["source_label_map"]
    require(isinstance(label_map, list) and len(label_map) == 4, "Invalid label map shape")
    for pair in label_map:
        naturals(pair, 2, "Invalid label conversion")
    require(label_map == [[1, 0], [2, 1], [3, 2], [4, 3]], "Wrong label map")
    require(report["relation_ids"] == ["getzler_1_8"] and
            report["relation_source"] == RELATION_SOURCE, "Wrong relation references")
    require(report["environment"]["sage"] == "10.9" and
            report["environment"]["admcycles"] == "1.4", "Wrong tool versions")
    require(isinstance(report["graphs"], list) and len(report["graphs"]) == 33,
            "Wrong graph count")
    graphs = [decode_graph(graph, i) for i, graph in enumerate(report["graphs"])]
    print(replay_source(report, graphs, hashlib.sha256(raw).hexdigest()), end="")


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"Getzler export failed: {error}", file=sys.stderr)
        sys.exit(1)
