#!/usr/bin/env python3
"""Emit claim-bound genus-one psi replay against the independent Lean frame.

The kernel checks raw graph isomorphisms, decorations, normalization, both
original rows, the held request and the exact witness. Geometry is separate.
"""

import argparse
import hashlib
import json
from pathlib import Path

from export_admcycles_certificate import (
    integer, rational_matrix, rational_vector, require, unique_object, vector,
)
from export_wdvv_certificate import naturals
from search_genus_one_psi import FRAME, RELATION_SOURCE

FIELDS = {"schema_version", "frame", "locus", "genus", "markings", "codimension",
          "normalization", "source_label_map", "relation_source", "generator_parameters",
          "graphs", "column_factors", "automorphism_counts", "rows", "requested", "witness",
          "environment", "producer_source_sha256", "exploration", "scope"}
PARAMETERS = [{"sigma": [1], "marking_groups": [[1, [0]]]},
              {"sigma": [], "marking_groups": [[1, [1]]]}]


def decode_graph(graph, index):
    require(isinstance(graph, dict) and set(graph) == {"index", "genus", "leg_vertices",
            "endpoints", "kappa", "leg_psi", "half_psi"}, "Unknown or missing graph field")
    require(integer(graph["index"], "Invalid graph index") == index, "Reordered graph slots")
    genera, edges = graph["genus"], graph["endpoints"]
    require(isinstance(genera, list) and 1 <= len(genera) <= 2, "Unsupported vertex count")
    require(isinstance(edges, list) and len(edges) <= 1, "Unsupported edge count")
    vertices, edge_count = len(genera), len(edges)
    naturals(genera, vertices, "Invalid vertex genus")
    require(all(v < vertices for v in naturals(graph["leg_vertices"], 1, "Invalid external incidence")),
            "External vertex out of range")
    for edge in edges:
        require(all(v < vertices for v in naturals(edge, 2, "Invalid edge pair")),
                "Edge vertex out of range")
    require(isinstance(graph["kappa"], list) and len(graph["kappa"]) == vertices,
            "Invalid kappa shape")
    require(isinstance(graph["half_psi"], list) and len(graph["half_psi"]) == edge_count,
            "Invalid node shape")
    for powers in graph["kappa"]:
        naturals(powers, 1, "Invalid kappa exponent")
    for powers in graph["half_psi"]:
        naturals(powers, 2, "Invalid node psi exponent")
    naturals(graph["leg_psi"], 1, "Invalid external psi exponent")
    return graph


def read_report(raw):
    report = json.loads(raw, object_pairs_hook=unique_object)
    require(isinstance(report, dict) and set(report) == FIELDS, "Unknown or missing report field")
    require(integer(report["schema_version"], "Invalid schema") == 1, "Wrong schema")
    require(report["frame"] == FRAME and report["locus"] == "full_stable", "Wrong frame/locus")
    require(integer(report["genus"], "Invalid genus") == 1 and
            integer(report["codimension"], "Invalid codimension") == 1, "Wrong genus/degree")
    require(naturals(report["markings"], 1, "Invalid markings") == [0], "Wrong label")
    require(report["normalization"] == "raw_gluing_pushforward", "Wrong normalization")
    label_map = report["source_label_map"]
    require(isinstance(label_map, list) and len(label_map) == 1, "Invalid label map")
    require(naturals(label_map[0], 2, "Invalid label map") == [1, 0], "Wrong label map")
    require(report["relation_source"] == RELATION_SOURCE, "Wrong relation source")
    # Compare canonical JSON so Boolean values cannot impersonate integers.
    require(json.dumps(report["generator_parameters"], sort_keys=True) ==
            json.dumps(PARAMETERS, sort_keys=True), "Wrong generator parameters")
    require(report["environment"]["sage"] == "10.9" and
            report["environment"]["admcycles"] == "1.4", "Wrong environment pin")
    require(isinstance(report["graphs"], list) and len(report["graphs"]) == 3, "Wrong graph count")
    graphs = [decode_graph(g, i) for i, g in enumerate(report["graphs"])]
    naturals(report["automorphism_counts"], 3, "Invalid automorphism counts")
    for key, count in (("column_factors", 3), ("requested", 3), ("witness", 2)):
        require(isinstance(report[key], list) and len(report[key]) == count, f"Wrong {key} size")
        rational_vector(report[key])
    rational_matrix(report["rows"], 2, 3)
    return report, graphs


def graph_source(index, graph):
    name = f"incomingGraph{index}"
    v, e = len(graph["genus"]), len(graph["endpoints"])
    nested = lambda rows: vector([vector([str(x) for x in row]) for row in rows])
    return "\n".join([
        f"/-- Raw incidence and vertex genera exported for column {index}. -/",
        f"def {name}Candidate : StableGraphCode.Candidate (Fin 1) {v} {e} where",
        f"  legVertex := {vector([str(x) for x in graph['leg_vertices']])}",
        f"  endpoint := {nested(graph['endpoints'])}",
        f"  genus := {vector([str(x) for x in graph['genus']])}", "",
        "/-- The incoming graph satisfies stability and total genus one. -/",
        f"theorem {name}Valid : {name}Candidate.Valid 1 := by decide +kernel", "",
        "/-- Incoming kappa, external psi and node psi exponents. -/",
        f"def {name}Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) {v} {e} 1 → ℕ",
        f"  | .inl (vertex, index) => ({nested(graph['kappa'])} : Fin {v} → Fin 1 → ℕ) vertex index",
        f"  | .inr (.inl label) => ({vector([str(x) for x in graph['leg_psi']])}) label",
        (f"  | .inr (.inr (edge, branch)) => ({nested(graph['half_psi'])}) edge branch" if e else
         "  | .inr (.inr (edge, _)) => Fin.elim0 edge"), "",
        "/-- The actual incoming decorated graph in the strata quotient. -/",
        f"def {name} : TautologicalStratum 1 (Fin 1) :=",
        "  .mk",
        "    (DecoratedStableGraph.toDecoration",
        f"      {name}Candidate {name}Valid {name}Exponents)",
        "    (DecoratedStableGraph.toDecoration_totalGenus",
        f"      {name}Candidate {name}Valid {name}Exponents)", "",
        "/-- The incoming decorated graph agrees with the independently held column. -/",
        f"theorem {name}_eq : {name} = GenusOnePsi.columns {index} :=",
        "  TautologicalStratum.mk_eq_mk_of_isomorphic?",
        "    (DecoratedStableGraph.toDecoration_totalGenus",
        f"      {name}Candidate {name}Valid {name}Exponents)",
        f"    (GenusOnePsi.graph_totalGenus {index})",
        "    (by simp only [GenusOnePsi.graph, DecoratedStableGraph.toDecoration_eq_mk];",
        "        decide +kernel)", "",
    ])


def replay_source(raw):
    report, graphs = read_report(raw)
    text = [
        "/-",
        "Copyright (c) 2026 JMA. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        "Authors: JMA", "-/", "module", "",
        "public import AxiomaticGW.Tautological.GenusOnePsi", "",
        "/-!", "# Candidate replay of the held genus-one psi relation", "",
        "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
        "Digest is provenance only. Geometric row validity remains an input.", "-/", "",
        "@[expose] public section", "", "namespace AxiomaticGW.GenusOnePsiReplay", "",
        *[graph_source(i, g) for i, g in enumerate(graphs)],
        "/-- Incoming columns in the original source order. -/",
        "def incomingColumns : Fin 3 → TautologicalStratum 1 (Fin 1) :=",
        "  ![incomingGraph0, incomingGraph1, incomingGraph2]", "",
        "/-- Reported raw graph automorphism counts. -/",
        "def incomingAutomorphisms : Fin 3 → ℕ :=",
        "  " + vector([str(x) for x in report["automorphism_counts"]]), "",
        "/-- Each reported automorphism count is checked against its held graph. -/",
        "theorem automorphisms_correct : ∀ i, incomingAutomorphisms i =",
        "    (GenusOnePsi.graph i).automorphismCount := by",
        "  simp only [GenusOnePsi.graph, DecoratedStableGraph.toDecoration_eq_mk]",
        "  decide +kernel", "",
        "/-- Original rows, normalization, requested equation and rational witness. -/",
        "def presentation : RelationCertificate.Presentation 1 (Fin 1) 2 3 where",
        "  columns := incomingColumns",
        "  columnFactors := " + rational_vector(report["column_factors"]),
        "  rows := " + rational_matrix(report["rows"], 2, 3),
        "  claimedRequest := " + rational_vector(report["requested"]),
        "  certificate := ⟨" + rational_vector(report["witness"]) + "⟩", "",
        "/-- All incoming data agree with the held frame and satisfy its exact equation. -/",
        "theorem accepted : GenusOnePsi.AcceptsExchange presentation := by",
        "  constructor", "  · refine ⟨?_, ?_, ?_, ?_⟩",
        "    · change incomingColumns = GenusOnePsi.columns",
        "      funext i", "      fin_cases i",
        "      · exact incomingGraph0_eq", "      · exact incomingGraph1_eq",
        "      · exact incomingGraph2_eq",
        "    · decide +kernel", "    · decide +kernel", "    · decide +kernel",
        "  · decide +kernel", "",
        "/-- The accepted requested relation lies in the span of the original rows. -/",
        "theorem requested_mem_relationSpan :",
        "    RelationCertificate.interpret GenusOnePsi.columns GenusOnePsi.requested ∈",
        "      RelationCertificate.relationSpan GenusOnePsi.columns GenusOnePsi.rows :=",
        "  RelationCertificate.acceptsPresentation_sound _ _ _ presentation accepted", "",
        "end AxiomaticGW.GenusOnePsiReplay", "",
    ]
    return "\n".join(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = replay_source(args.report.read_bytes())
    if args.check:
        require(args.output is not None and args.output.read_text() == result,
                "Saved replay differs from generated source")
    elif args.output:
        args.output.write_text(result)
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
