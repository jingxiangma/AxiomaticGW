#!/usr/bin/env python3
"""Decode untrusted BP data and emit kernel replay against the separately held claim.

Ordinary Python and Lean suffice. Incoming target/source graphs, coefficients,
normalizations and operation tables are emitted as actual data, then checked.
Sage search, hashes and numerical intersection diagnostics supply no axioms.
Failed closed checks report a short message: printing their fully expanded
graph tables can itself exhaust Lean's diagnostic budget. The fallback only
fails; it supplies no proof. Negative tests separately prove counterexamples.
"""
import argparse
import hashlib
import json
from pathlib import Path
import textwrap

from export_admcycles_certificate import (
    integer, rational, rational_text, rational_matrix, rational_vector, require, unique_object, vector,
)
from export_wdvv_certificate import naturals
from export_genus_two_psi_square import held_metadata, SOURCE_PINS
from search_belorousski_pandharipande import FRAME, RELATION_SOURCE, PUBLISHED_SOURCE, SOURCE_FAMILIES

FIELDS = {'requested', 'schema_version', 'pushforward_to_monomial_off_diagonal', 'automorphism_counts', 'rows', 'original_rows', 'normalization', 'graphs', 'relation_source', 'monomial_to_pushforward_off_diagonal', 'generator_provenance', 'published_source', 'unsymmetrized_rows', 'source_label_map', 'environment', 'witness', 'locus', 'published_terms', 'codimension', 'column_factors', 'exploration', 'genus', 'producer_source_sha256', 'permutation_destinations', 'source_families', 'scope', 'markings', 'frame'}
GENERATOR_METADATA = [{'kind': 'interior',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]], [3, [0]]], 'sigma': [1, 1, 1]},
  'upstream_index': 1},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [1]], [2, [0]], [3, [0]]], 'sigma': [1, 1]},
  'upstream_index': 2},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [1]], [2, [1]], [3, [0]]], 'sigma': [1]},
  'upstream_index': 5},
 {'kind': 'interior',
  'parameter': {'marking_groups': [[1, [1]], [2, [1]], [3, [1]]], 'sigma': []},
  'upstream_index': 9},
 {'base_index': 4,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]]], 'sigma': []},
  'source_family': 0,
  'upstream_index': 16,
  'vertex_one_based': 2},
 {'base_index': 7,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]], [3, [0]], [4, [0]]], 'sigma': [1, 1]},
  'source_family': 1,
  'upstream_index': 19,
  'vertex_one_based': 1},
 {'base_index': 7,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [1]], [2, [0]], [3, [0]], [4, [0]]], 'sigma': [1]},
  'source_family': 1,
  'upstream_index': 20,
  'vertex_one_based': 1},
 {'base_index': 7,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]], [3, [0]], [4, [1]]], 'sigma': [1]},
  'source_family': 1,
  'upstream_index': 23,
  'vertex_one_based': 1},
 {'base_index': 7,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]]], 'sigma': []},
  'source_family': 2,
  'upstream_index': 31,
  'vertex_one_based': 2},
 {'base_index': 8,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]]], 'sigma': [1]},
  'source_family': 3,
  'upstream_index': 32,
  'vertex_one_based': 1},
 {'base_index': 8,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [1]]], 'sigma': []},
  'source_family': 3,
  'upstream_index': 33,
  'vertex_one_based': 1},
 {'base_index': 8,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]], [3, [0]], [4, [0]]], 'sigma': [1]},
  'source_family': 4,
  'upstream_index': 34,
  'vertex_one_based': 2},
 {'base_index': 8,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [1]], [2, [0]], [3, [0]], [4, [0]]], 'sigma': []},
  'source_family': 4,
  'upstream_index': 35,
  'vertex_one_based': 2},
 {'base_index': 8,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]], [3, [0]], [4, [1]]], 'sigma': []},
  'source_family': 4,
  'upstream_index': 38,
  'vertex_one_based': 2},
 {'base_index': 9,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]]], 'sigma': [1]},
  'source_family': 5,
  'upstream_index': 39,
  'vertex_one_based': 1},
 {'base_index': 9,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [1]], [2, [0]]], 'sigma': []},
  'source_family': 5,
  'upstream_index': 40,
  'vertex_one_based': 1},
 {'base_index': 9,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]], [2, [1]]], 'sigma': []},
  'source_family': 5,
  'upstream_index': 41,
  'vertex_one_based': 1},
 {'base_index': 9,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]], [3, [0]]], 'sigma': [1]},
  'source_family': 6,
  'upstream_index': 42,
  'vertex_one_based': 2},
 {'base_index': 9,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [1]], [2, [0]], [3, [0]]], 'sigma': []},
  'source_family': 6,
  'upstream_index': 43,
  'vertex_one_based': 2},
 {'base_index': 9,
  'kind': 'separating',
  'parameter': {'marking_groups': [[1, [0]], [2, [0]], [3, [1]]], 'sigma': []},
  'source_family': 6,
  'upstream_index': 45,
  'vertex_one_based': 2}]
SOURCE_SIZES = [7, 8, 4, 3, 17, 5, 9]


def decode_graph(g, n, index=None):
    fields = {"genus", "leg_vertices", "endpoints", "kappa", "leg_psi", "half_psi"}
    if index is not None:
        fields.add("index")
    require(isinstance(g, dict) and set(g) == fields, "Unknown or missing graph field")
    if index is not None:
        require(integer(g["index"], "Invalid graph index") == index, "Reordered graph slots")
    require(isinstance(g["genus"], list) and 1 <= len(g["genus"]) <= 3, "Invalid vertex count")
    require(isinstance(g["endpoints"], list) and len(g["endpoints"]) <= 2, "Invalid edge count")
    v, e = len(g["genus"]), len(g["endpoints"])
    require(all(x <= 2 for x in naturals(g["genus"], v, "Invalid genus")), "Unsupported genus")
    require(all(x < v for x in naturals(g["leg_vertices"], n, "Invalid external incidence")),
            "External vertex out of range")
    for edge in g["endpoints"]:
        require(all(x < v for x in naturals(edge, 2, "Invalid edge")), "Edge vertex out of range")
    require(isinstance(g["kappa"], list) and len(g["kappa"]) == v, "Invalid kappa shape")
    require(isinstance(g["half_psi"], list) and len(g["half_psi"]) == e, "Invalid node shape")
    for powers in g["kappa"] + g["half_psi"]:
        require(all(x <= 2 for x in naturals(powers, 2, "Invalid decoration")),
                "Decoration out of range")
    require(all(x <= 2 for x in naturals(g["leg_psi"], n, "Invalid external decoration")),
            "External decoration out of range")
    return g


def read_report(raw):
    d = json.loads(raw, object_pairs_hook=unique_object)
    require(isinstance(d, dict) and set(d) == FIELDS, "Unknown or missing report field")
    require(integer(d["schema_version"], "Invalid schema") == 1, "Wrong schema")
    require(d["frame"] == FRAME and d["locus"] == "full_stable", "Wrong frame/locus")
    require(integer(d["genus"], "Invalid genus") == 2 and
            integer(d["codimension"], "Invalid codimension") == 2, "Wrong genus/degree")
    held_metadata(d["markings"], [0, 1, 2], "Wrong marking set")
    held_metadata(d["source_label_map"], [[1, 0], [2, 1], [3, 2]], "Wrong source labels")
    require(d["normalization"] == "raw_gluing_pushforward", "Wrong normalization")
    require(d["relation_source"] == RELATION_SOURCE and d["published_source"] == PUBLISHED_SOURCE,
            "Wrong mathematical source")
    held_metadata(d["producer_source_sha256"], SOURCE_PINS, "Wrong producer pins")
    env = d["environment"]
    require(isinstance(env, dict) and set(env) == {"sage", "admcycles", "python", "architecture"},
            "Invalid environment fields")
    require(env["sage"] == "10.9" and env["admcycles"] == "1.4" and
            all(isinstance(v, str) for v in env.values()), "Wrong environment pin")
    require(isinstance(d["graphs"], list) and len(d["graphs"]) == 100, "Wrong raw frame size")
    for i, g in enumerate(d["graphs"]):
        decode_graph(g, 3, i)
    naturals(d["automorphism_counts"], 100, "Invalid graph orders")
    for field, size in (("column_factors", 100), ("requested", 100), ("witness", 20)):
        require(isinstance(d[field], list) and len(d[field]) == size, "Wrong vector size")
        rational_vector(d[field])
    for field in ("rows", "original_rows", "unsymmetrized_rows"):
        rational_matrix(d[field], 20, 100)
    require(isinstance(d["permutation_destinations"], list) and
            len(d["permutation_destinations"]) == 6, "Wrong permutation count")
    for row in d["permutation_destinations"]:
        require(all(i < 100 for i in naturals(row, 100, "Invalid permutation row")),
                "Permutation destination out of range")
    for field in ("pushforward_to_monomial_off_diagonal", "monomial_to_pushforward_off_diagonal"):
        correction = d[field]
        require(isinstance(correction, list) and len(correction) == 1 and
                isinstance(correction[0], list) and len(correction[0]) == 3, "Invalid kappa map")
        require(all(i < 100 for i in naturals(correction[0][:2], 2, "Invalid kappa slot")),
                "Kappa slot out of range")
        rational(correction[0][2])
    require(d["pushforward_to_monomial_off_diagonal"][0][:2] ==
            d["monomial_to_pushforward_off_diagonal"][0][:2], "Different inverse kappa slots")
    require(isinstance(d["published_terms"], list) and len(d["published_terms"]) == 20,
            "Wrong published term count")
    for term in d["published_terms"]:
        require(isinstance(term, dict) and set(term) ==
                {"coefficient", "graph", "automorphism", "destinations"}, "Invalid published term")
        decode_graph(term["graph"], 3)
        rational(term["coefficient"])
        require(integer(term["automorphism"], "Invalid published graph order") > 0,
                "Nonpositive graph order")
        require(all(i < 100 for i in naturals(term["destinations"], 6, "Invalid marking orbit")),
                "Orbit destination out of range")
    require(isinstance(d["source_families"], list) and len(d["source_families"]) == 7,
            "Wrong source family count")
    for f, (g, n), size in zip(d["source_families"], SOURCE_FAMILIES, SOURCE_SIZES):
        require(isinstance(f, dict) and set(f) == {"genus", "markings", "codimension", "graphs"},
                "Invalid source family")
        held_metadata([f["genus"], f["markings"], f["codimension"]], [g, n, 1], "Wrong source space")
        require(isinstance(f["graphs"], list) and len(f["graphs"]) == size, "Wrong source frame size")
        for i, graph in enumerate(f["graphs"]):
            decode_graph(graph, n, i)
    require(isinstance(d["generator_provenance"], list) and len(d["generator_provenance"]) == 20,
            "Wrong original generator count")
    family_destinations = {}
    for p, meta in zip(d["generator_provenance"], GENERATOR_METADATA):
        extra = set() if meta["kind"] == "interior" else {"coefficients", "destinations"}
        require(isinstance(p, dict) and set(p) == set(meta) | extra, "Invalid generator fields")
        held_metadata({k: p[k] for k in meta}, meta, "Wrong original generator provenance")
        if extra:
            b = meta["source_family"]
            size = SOURCE_SIZES[b]
            require(isinstance(p["coefficients"], list) and len(p["coefficients"]) == size,
                    "Wrong component row size")
            rational_vector(p["coefficients"])
            require(all(i < 100 for i in naturals(p["destinations"], size, "Invalid source map")),
                    "Source destination out of range")
            require(b not in family_destinations or family_destinations[b] == p["destinations"],
                    "Inconsistent copies of one gluing operation")
            family_destinations[b] = p["destinations"]
    diag = d["exploration"]
    require(isinstance(diag, dict) and set(diag) == {"online_lookup", "cache_ephemeral",
            "raw_basis_identity_checked", "full_row_count", "selected_row_count", "selected_rank",
            "intersection_tests"}, "Wrong exploration fields")
    require(diag["online_lookup"] is False and diag["cache_ephemeral"] is True and
            diag["raw_basis_identity_checked"] is True, "Exploration was not offline")
    for field, expected in (("full_row_count", 65), ("selected_row_count", 20), ("selected_rank", 20)):
        require(integer(diag[field], "Invalid diagnostic count") == expected, "Wrong diagnostic count")
    require(isinstance(diag["intersection_tests"], list) and len(diag["intersection_tests"]) == 15,
            "Wrong diagnostic test count")
    rational_vector(diag["intersection_tests"])
    require(isinstance(d["scope"], str), "Invalid scope text")
    return d


def vec(a):
    return vector([str(x) for x in a])


def nested(a):
    return vector([vec(x) for x in a])


def graph_expression(g, genus, n):
    candidate = ("(⟨" + vec(g["leg_vertices"]) + ", " + nested(g["endpoints"]) +
                 ", " + vec(g["genus"]) + "⟩ : StableGraphCode.Candidate (Fin " + str(n) +
                 ") " + str(len(g["genus"])) + " " + str(len(g["endpoints"])) + ")")
    return (f"BelorousskiPandharipande.tableGraph {genus}\n      {candidate}\n" +
            "      (by decide +kernel)\n      " + nested(g["kappa"]) + " " +
            vec(g["leg_psi"]) + " " + nested(g["half_psi"]))


def dependent_vector(entries):
    result = "fun i ↦ Fin.elim0 i"
    for entry in reversed(entries):
        result = "Fin.cases (" + entry + ") (\n    " + result + ")"
    return result


def frame_source(name, graphs, genus, n, held_graph, held_columns):
    return "\n".join([
        "/-- Actual incoming graph incidence and all decoration powers. -/",
        f"def {name}Graphs : Fin {len(graphs)} → DecoratedStableGraph (Fin {n}) :=",
        "  " + vector([graph_expression(g, genus, n) for g in graphs]), "",
        "/-- Connectedness and stability were checked by each constructor; genus is retained. -/",
        f"theorem {name}Genus (i : Fin {len(graphs)}) : ({name}Graphs i).graph.totalGenus = {genus} := by",
        "  fin_cases i <;> decide +kernel", "",
        "/-- Incoming graph classes use the existing semantic quotient. -/",
        f"def {name}Columns (i : Fin {len(graphs)}) : TautologicalStratum {genus} (Fin {n}) :=",
        f"  .mk ({name}Graphs i) ({name}Genus i)", "",
        "-- The diagnostic branch is exercised by the negative exchange tests.",
        "set_option linter.unusedTactic false in",
        "set_option linter.unreachableTactic false in",
        "/-- Semantic equality is checked against the independently held frame. -/",
        f"theorem {name}Columns_eq : {name}Columns = {held_columns} := by",
        f"  simp only [funext_iff, {name}Columns, {held_columns}, {name}Graphs, {held_graph},",
        "    BelorousskiPandharipande.tableGraph, DecoratedStableGraph.toDecoration_eq_mk]",
        "  first", "  | decide +kernel",
        '  | fail "BP incoming graph frame check did not close"', "",
    ])


def replay_source(raw):
    d = read_report(raw)
    b = "BelorousskiPandharipande"
    text = ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.", "Authors: JMA", "-/",
        "module", "", f"public import AxiomaticGW.Tautological.{b}", "", "/-!",
        "# Offline incoming replay for the complete published BP equation", "",
        "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
        "The digest records provenance; graph and rational equalities are kernel obligations.",
        "-/", "", "@[expose] public section", "", f"namespace AxiomaticGW.{b}Replay", "",
        frame_source("incoming", d["graphs"], 2, 3, b + ".graph", b + ".columns"),
        frame_source("paper", [t["graph"] for t in d["published_terms"]], 2, 3,
                     b + ".paperGraph", b + ".paperStratum"),
        "/-- Actual incoming component graph frames, including the one-point elliptic input. -/",
        f"def sourceGraphs : (b : Fin 7) → Fin ({b}.sourceSize b) →",
        f"    DecoratedStableGraph (Fin ({b}.sourceArity b)) :=",
        "  " + dependent_vector([vector([graph_expression(g, f["genus"], f["markings"])
                                         for g in f["graphs"]]) for f in d["source_families"]]), "",
        "/-- Arithmetic genus is checked for every incoming component column. -/",
        f"theorem sourceGraphs_genus (b : Fin 7) (i : Fin ({b}.sourceSize b)) :",
        f"    (sourceGraphs b i).graph.totalGenus = {b}.sourceGenus b := by",
        "  fin_cases b <;> fin_cases i <;> decide +kernel", "",
        "/-- Actual incoming source graph classes. -/",
        f"def sourceColumns (b : Fin 7) (i : Fin ({b}.sourceSize b)) :",
        f"    TautologicalStratum ({b}.sourceGenus b) (Fin ({b}.sourceArity b)) :=",
        "  .mk (sourceGraphs b i) (sourceGraphs_genus b i)", "",
        "-- The diagnostic branch is exercised by the negative exchange tests.",
        "set_option linter.unusedTactic false in",
        "set_option linter.unreachableTactic false in",
        "/-- Source incidence and decorations agree semantically with the held component frames. -/",
        f"theorem sourceColumns_eq : sourceColumns = {b}.sourceColumns := by",
        f"  simp only [funext_iff, sourceColumns, {b}.sourceColumns, sourceGraphs, {b}.sourceGraph,",
        f"    {b}.tableGraph, GenusOnePsi.graph, DecoratedStableGraph.toDecoration_eq_mk]",
        "  first", "  | decide +kernel",
        '  | fail "BP incoming source graph check did not close"', "",
        "/-- Incoming component rows, preserving their separately held source families. -/",
        f"def sourceRows : (i : Fin 16) → RelationCertificate.Coordinates ({b}.sourceSize ({b}.sourceFamily i)) :=",
        "  " + dependent_vector([rational_vector(p["coefficients"]) for p in d["generator_provenance"][4:]]), "",
        "/-- Incoming source operation tables. -/",
        f"def sourceDestinations : (b : Fin 7) → Fin ({b}.sourceSize b) → Fin 100 :=",
        "  " + dependent_vector([vec(next(p["destinations"] for p in d["generator_provenance"][4:]
                                         if p["source_family"] == i)) for i in range(7)]), "",
        "/-- Actual incoming symmetric row coordinates. -/",
        "def incomingRows : Fin 20 → RelationCertificate.Coordinates 100 := " + rational_matrix(d["rows"], 20, 100), "",
        "/-- Actual original pushforward-kappa coordinates. -/",
        "def incomingOriginalRows : Fin 20 → RelationCertificate.Coordinates 100 := " + rational_matrix(d["original_rows"], 20, 100), "",
        "/-- Actual unsymmetrized monomial-kappa coordinates. -/",
        "def incomingUnsymmetrizedRows : Fin 20 → RelationCertificate.Coordinates 100 := " + rational_matrix(d["unsymmetrized_rows"], 20, 100), "",
        "/-- Every incoming mathematical field is retained for acceptance checking. -/",
        f"def exchange : {b}.Exchange where",
        "  presentation := {", "    columns := incomingColumns",
        "    columnFactors := " + rational_vector(d["column_factors"]),
        "    rows := incomingRows",
        "    claimedRequest := " + rational_vector(d["requested"]),
        "    certificate := ⟨" + rational_vector(d["witness"]) + "⟩ }",
        "  originalRows := incomingOriginalRows",
        "  unsymmetrizedRows := incomingUnsymmetrizedRows",
        "  conversionSource := " + str(d["pushforward_to_monomial_off_diagonal"][0][0]),
        "  conversionTarget := " + str(d["pushforward_to_monomial_off_diagonal"][0][1]),
        "  forwardCoefficient := " + rational_text(rational(d["pushforward_to_monomial_off_diagonal"][0][2])),
        "  backwardCoefficient := " + rational_text(rational(d["monomial_to_pushforward_off_diagonal"][0][2])),
        "  automorphisms := " + vec(d["automorphism_counts"]), "  paperColumns := paperColumns",
        "  paperCoefficients := " + rational_vector([p["coefficient"] for p in d["published_terms"]]),
        "  paperOrders := " + vec([p["automorphism"] for p in d["published_terms"]]),
        "  paperDestinations := " + nested([p["destinations"] for p in d["published_terms"]]),
        "  permutationDestinations := " + nested(d["permutation_destinations"]),
        "  sourceColumns := sourceColumns", "  sourceRows := sourceRows",
        "  sourceDestinations := sourceDestinations",
        "  generatorReferences := " + vec([p["upstream_index"] for p in d["generator_provenance"]]), "",
        "set_option maxHeartbeats 2000000 in",
        "-- Kernel acceptance compares the complete three 20-by-100 tables and all operation data.",
        "-- The diagnostic branch is exercised by the negative exchange tests.",
        "set_option linter.unusedTactic false in",
        "set_option linter.unreachableTactic false in",
        "/-- Incoming graphs and exact arithmetic prove acceptance for the caller-held published claim. -/",
        f"theorem accepted : {b}.AcceptsExchange exchange := by",
        "  refine ⟨⟨⟨incomingColumns_eq, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,",
        "    paperColumns_eq, ?_, ?_, ?_, ?_, sourceColumns_eq, ?_, ?_, ?_⟩ <;>",
        "    first", "    | decide +kernel",
        '    | fail "BP incoming coordinate check did not close"', "",
        "/-- Offline replay proves the original published equation belongs to the fixed row span. -/",
        "theorem requested_mem_relationSpan :",
        f"    RelationCertificate.interpret {b}.columns {b}.requested ∈",
        f"      RelationCertificate.relationSpan {b}.columns {b}.rows :=",
        "  RelationCertificate.acceptsPresentation_sound _ _ _ exchange.presentation accepted.1", "",
        f"end AxiomaticGW.{b}Replay", ""]
    return "\n".join(textwrap.fill(line, width=98,
        subsequent_indent=" " * (len(line) - len(line.lstrip()) + 2),
        break_long_words=False, break_on_hyphens=False) if len(line) > 100 else line
        for line in "\n".join(text).splitlines()) + "\n"


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
