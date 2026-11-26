#!/usr/bin/env python3
"""Replay incoming marked genus-two data against a separate, fixed Lean frame.

Graph decorations, raw normalization, both coordinate systems, the requested
psi-product equation, the boundary side and the witness are kernel checked.
Producer pins and source parameters are provenance, not geometric proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import textwrap

from export_admcycles_certificate import (
    integer, rational_matrix, rational_vector, require, unique_object, vector,
)
from export_wdvv_certificate import naturals
from search_genus_two_psi_product import FRAME, RELATION_SOURCE

FIELDS = {'automorphism_counts',
 'boundary',
 'codimension',
 'column_factors',
 'environment',
 'exploration',
 'frame',
 'generator_provenance',
 'genus',
 'graphs',
 'locus',
 'markings',
 'monomial_to_pushforward',
 'normalization',
 'original_rows',
 'producer_source_sha256',
 'pushforward_to_monomial',
 'relation_source',
 'requested',
 'rows',
 'schema_version',
 'scope',
 'source_label_map',
 'witness'}
PROVENANCE = [{'kind': 'interior',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]]], 'sigma': [3]},
  'upstream_index': 0},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]]], 'sigma': [1, 1, 1]},
  'upstream_index': 1},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [1]], [2, [0]]], 'sigma': [1, 1]},
  'upstream_index': 2},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [0]], [2, [1]]], 'sigma': [1, 1]},
  'upstream_index': 3},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [1]], [2, [1]]], 'sigma': [1]},
  'upstream_index': 4},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [3]], [2, [0]]], 'sigma': []},
  'upstream_index': 5},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [0]], [2, [3]]], 'sigma': []},
  'upstream_index': 6},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]]], 'sigma': [1]},
  'upstream_index': 7},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [1]], [2, [0]]], 'sigma': []},
  'upstream_index': 8},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [0]], [2, [1]]], 'sigma': []},
  'upstream_index': 9},
 {'base_index': 3,
  'coefficients': [[-30, 1], [30, 1], [42, 1], [3, 1]],
  'destinations': [7, 8, 19, 29],
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]]], 'sigma': []},
  'source_arity': 1,
  'source_codimension': 1,
  'source_genus': 2,
  'upstream_index': 10,
  'vertex_one_based': 2},
 {'base_index': 4,
  'coefficients': [[102, 1], [-30, 1], [-3, 1]],
  'destinations': [23, 24, 33],
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]]], 'sigma': [1]},
  'source_arity': 1,
  'source_codimension': 1,
  'source_genus': 1,
  'upstream_index': 11,
  'vertex_one_based': 1},
 {'base_index': 4,
  'coefficients': [[81, 2],
                   [-45, 2],
                   [-45, 2],
                   [-45, 2],
                   [9, 2],
                   [9, 2],
                   [9, 2],
                   [-27, 2],
                   [-9, 4]],
  'destinations': [9, 10, 11, 12, 20, 21, 19, 22, 36],
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]], [3, [0]]], 'sigma': [1]},
  'source_arity': 3,
  'source_codimension': 1,
  'source_genus': 1,
  'upstream_index': 13,
  'vertex_one_based': 2}]
SOURCE_PINS = {'admcycles.py': '19e9e77c58299b387abadab76f2e1f1b1b2b63808f3dbbd0e44499a930db9a1b',
 'algebra.py': '7d684ffc9c04d77434a9a2e9d52d4a7c79b159693bc5d5989ee443cbdcc724d1',
 'graph.py': '3c4c4f833989177f055710c067e77817113efd4062cdab105e56162155949481',
 'relations.py': 'bd9f1f2476ceed08d745fce684cced8950b41746644162594dd00e7ee4b6b1a5',
 'stable_graph.py': 'aa9b81ae274660b2d44cf474390a8b0c3a7865cfa6deaa06d005ae96dfdbd3ca',
 'tautological_ring.py': 'c9cf9b46fa8c7f2207d6d0ebc3f3565518f6f29d324bb6b280c1626a772bbd12'}


def held_metadata(value, held, message):
    # Booleans must not impersonate integer-valued provenance.
    require(json.dumps(value, sort_keys=True) == json.dumps(held, sort_keys=True), message)


def decode_graph(graph, index):
    require(isinstance(graph, dict) and set(graph) == {"index", "genus", "leg_vertices",
            "endpoints", "kappa", "leg_psi", "half_psi"}, "Unknown or missing graph field")
    require(integer(graph["index"], "Invalid graph index") == index, "Reordered graph slots")
    genera, edges = graph["genus"], graph["endpoints"]
    require(isinstance(genera, list) and 1 <= len(genera) <= 3, "Unsupported vertex count")
    require(isinstance(edges, list) and len(edges) <= 2, "Unsupported edge count")
    vertices, edge_count = len(genera), len(edges)
    require(all(g <= 2 for g in naturals(genera, vertices, "Invalid vertex genus")),
            "Genus exceeds frame bound")
    require(all(v < vertices for v in naturals(graph["leg_vertices"], 2, "Invalid external incidence")),
            "External vertex out of range")
    for edge in edges:
        require(all(v < vertices for v in naturals(edge, 2, "Invalid edge pair")),
                "Edge vertex out of range")
    require(isinstance(graph["kappa"], list) and len(graph["kappa"]) == vertices,
            "Invalid kappa shape")
    require(isinstance(graph["half_psi"], list) and len(graph["half_psi"]) == edge_count,
            "Invalid node shape")
    for powers in graph["kappa"] + graph["half_psi"]:
        require(all(p <= 2 for p in naturals(powers, 2, "Invalid decoration exponent")),
                "Decoration exceeds frame bound")
    require(all(p <= 2 for p in naturals(graph["leg_psi"], 2, "Invalid external psi exponent")),
            "External exponent exceeds frame bound")
    return graph


def read_report(raw):
    report = json.loads(raw, object_pairs_hook=unique_object)
    require(isinstance(report, dict) and set(report) == FIELDS, "Unknown or missing report field")
    require(integer(report["schema_version"], "Invalid schema") == 1, "Wrong schema")
    require(report["frame"] == FRAME and report["locus"] == "full_stable", "Wrong frame/locus")
    require(integer(report["genus"], "Invalid genus") == 2 and
            integer(report["codimension"], "Invalid degree") == 2, "Wrong genus/degree")
    require(naturals(report["markings"], 2, "Invalid markings") == [0, 1], "Wrong labels")
    require(report["normalization"] == "raw_gluing_pushforward", "Wrong normalization")
    held_metadata(report["source_label_map"], [[1, 0], [2, 1]], "Wrong label map")
    require(report["relation_source"] == RELATION_SOURCE, "Wrong relation source")
    held_metadata(report["generator_provenance"], PROVENANCE, "Wrong source provenance")
    held_metadata(report["producer_source_sha256"], SOURCE_PINS, "Wrong producer source pins")
    env = report["environment"]
    require(isinstance(env, dict) and set(env) == {"sage", "admcycles", "python", "architecture"},
            "Invalid environment metadata")
    require(env["sage"] == "10.9" and env["admcycles"] == "1.4" and
            all(isinstance(v, str) for v in env.values()), "Wrong environment pin")
    require(isinstance(report["graphs"], list) and len(report["graphs"]) == 38, "Wrong graph count")
    graphs = [decode_graph(g, i) for i, g in enumerate(report["graphs"])]
    naturals(report["automorphism_counts"], 38, "Invalid automorphism counts")
    for key, count in (("column_factors", 38), ("requested", 38), ("boundary", 38), ("witness", 13)):
        require(isinstance(report[key], list) and len(report[key]) == count, f"Wrong {key} size")
        rational_vector(report[key])
    for key, size in (("rows", 13), ("original_rows", 13), ("pushforward_to_monomial", 38),
                      ("monomial_to_pushforward", 38)):
        rational_matrix(report[key], size, 38)
    diag = report["exploration"]
    require(isinstance(diag, dict) and set(diag) == {"online_lookup", "cache_ephemeral",
            "intersection_tests"}, "Invalid exploration metadata")
    require(diag["online_lookup"] is False and diag["cache_ephemeral"] is True,
            "Search must use offline ephemeral caches")
    require(isinstance(diag["intersection_tests"], list) and len(diag["intersection_tests"]) == 4,
            "Wrong diagnostic count")
    rational_vector(diag["intersection_tests"])
    require(isinstance(report["scope"], str), "Invalid scope text")
    return report, graphs


def graph_source(index, graph):
    name = f"incomingGraph{index}"
    v, e = len(graph["genus"]), len(graph["endpoints"])
    nested = lambda rows: vector([vector([str(x) for x in row]) for row in rows])
    return "\n".join([
        f"/-- Actual incoming incidence and genera for column {index}. -/",
        f"def {name}Candidate : StableGraphCode.Candidate (Fin 2) {v} {e} where",
        f"  legVertex := {vector([str(x) for x in graph['leg_vertices']])}",
        f"  endpoint := {nested(graph['endpoints'])}",
        f"  genus := {vector([str(x) for x in graph['genus']])}", "",
        "/-- Stability and arithmetic genus are kernel checked. -/",
        f"theorem {name}Valid : {name}Candidate.Valid 2 := by decide +kernel", "",
        "/-- Incoming kappa powers, external cotangent powers and node branch powers. -/",
        f"def {name}Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) {v} {e} 2 → ℕ",
        f"  | .inl (vertex, index) => ({nested(graph['kappa'])} : Fin {v} → Fin 2 → ℕ) vertex index",
        f"  | .inr (.inl label) => ({vector([str(x) for x in graph['leg_psi']])}) label",
        (f"  | .inr (.inr (edge, branch)) => ({nested(graph['half_psi'])}) edge branch" if e else
         "  | .inr (.inr (edge, _)) => Fin.elim0 edge"), "",
        "/-- The incoming decorated graph in the existing isomorphism quotient. -/",
        f"def {name} : TautologicalStratum 2 (Fin 2) :=",
        "  .mk",
        "    (DecoratedStableGraph.toDecoration",
        f"      {name}Candidate {name}Valid {name}Exponents)",
        "    (DecoratedStableGraph.toDecoration_totalGenus",
        f"      {name}Candidate {name}Valid {name}Exponents)", "",
        "/-- Incoming decorations and incidence agree with the independently held column. -/",
        f"theorem {name}_eq : {name} = GenusTwoPsiProduct.columns {index} :=",
        "  TautologicalStratum.mk_eq_mk_of_isomorphic?",
        "    (DecoratedStableGraph.toDecoration_totalGenus",
        f"      {name}Candidate {name}Valid {name}Exponents)",
        f"    (GenusTwoPsiProduct.graph_totalGenus {index})",
        "    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,",
        "          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)", "",
    ])


def replay_source(raw):
    report, graphs = read_report(raw)
    text = [
        "/-", "Copyright (c) 2026 JMA. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        "Authors: JMA", "-/", "module", "",
        "public import AxiomaticGW.Tautological.GenusTwoPsiProduct", "",
        "/-!", "# Incoming replay of the held marked genus-two psi-product relation", "",
        "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
        "The digest records provenance only. Geometric validity remains explicit.", "-/", "",
        "@[expose] public section", "", "namespace AxiomaticGW.GenusTwoPsiProductReplay", "",
        *[graph_source(i, g) for i, g in enumerate(graphs)],
        "/-- Actual incoming columns, preserving the original source order. -/",
        "def incomingColumns : Fin 38 → TautologicalStratum 2 (Fin 2) :=",
        "  " + vector([f"incomingGraph{i}" for i in range(38)]), "",
        "/-- Incoming mathematical data in both rational coordinate systems. -/",
        "def exchange : GenusTwoPsiProduct.Exchange where",
        "  presentation := {",
        "    columns := incomingColumns",
        "    columnFactors := " + rational_vector(report["column_factors"]),
        "    rows := " + rational_matrix(report["rows"], 13, 38),
        "    claimedRequest := " + rational_vector(report["requested"]),
        "    certificate := ⟨" + rational_vector(report["witness"]) + "⟩ }",
        "  sourceRows := " + rational_matrix(report["original_rows"], 13, 38),
        "  sourceToMonomial := " + rational_matrix(report["pushforward_to_monomial"], 38, 38),
        "  monomialToSource := " + rational_matrix(report["monomial_to_pushforward"], 38, 38),
        "  claimedBoundary := " + rational_vector(report["boundary"]),
        "  automorphisms := " + vector([str(x) for x in report["automorphism_counts"]]), "",
        "/-- All incoming fields are bound to the held claim and the witness is checked. -/",
        "theorem accepted : GenusTwoPsiProduct.AcceptsExchange exchange := by",
        "  constructor", "  · constructor", "    · refine ⟨?_, ?_, ?_, ?_⟩",
        "      · change incomingColumns = GenusTwoPsiProduct.columns",
        "        funext i", "        fin_cases i",
        *[f"        · exact incomingGraph{i}_eq" for i in range(38)],
        "      · decide +kernel", "      · decide +kernel", "      · decide +kernel",
        "    · decide +kernel",
        "  · refine ⟨?_, ?_, ?_, ?_, ?_⟩",
        "    · decide +kernel", "    · decide +kernel", "    · decide +kernel",
        "    · decide +kernel",
        "    · simp only [GenusTwoPsiProduct.automorphismOrders_correct]",
        "      decide +kernel", "",
        "/-- The actual accepted request is in the span of the held original rows. -/",
        "theorem requested_mem_relationSpan :",
        "    RelationCertificate.interpret GenusTwoPsiProduct.columns GenusTwoPsiProduct.requested ∈",
        "      RelationCertificate.relationSpan GenusTwoPsiProduct.columns GenusTwoPsiProduct.rows :=",
        "  RelationCertificate.acceptsPresentation_sound _ _ _ exchange.presentation accepted.1", "",
        "end AxiomaticGW.GenusTwoPsiProductReplay", "",
    ]
    return "\n".join(textwrap.fill(line, width=98,
        subsequent_indent=" " * (len(line) - len(line.lstrip()) + 2),
        break_long_words=False, break_on_hyphens=False) if len(line) > 100 else line
        for line in ("\n".join(text)).splitlines()) + "\n"


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
