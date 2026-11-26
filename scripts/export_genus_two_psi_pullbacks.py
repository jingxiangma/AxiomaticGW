#!/usr/bin/env python3
"""Emit offline coordinate replay against actual held Lean pullback constructions."""
import argparse
import hashlib
import json
from pathlib import Path
import textwrap

from export_admcycles_certificate import (integer, rational, rational_vector, require, unique_object)

SOURCE_PINS = {'belorousski-pandharipande.json': '5868b2f3ef1e5a45e6175b6349566b72c778f4ab028ef941b43498fd0ee8d1bc',
 'genus-two-psi-product-exploration.json': 'b22e8c432358044fec84188b96a5747cdf3ff14d4317686ebe6c661d62fe85b0',
 'genus-two-psi-square-exploration.json': '6b9c75fd1555575fd036348e943881f6ba5cb8e83b7b7f51e64f7448286e5e1d'}
PRODUCER_PINS = {'admcycles.py': '19e9e77c58299b387abadab76f2e1f1b1b2b63808f3dbbd0e44499a930db9a1b',
 'stable_graph.py': 'aa9b81ae274660b2d44cf474390a8b0c3a7865cfa6deaa06d005ae96dfdbd3ca',
 'tautological_ring.py': 'c9cf9b46fa8c7f2207d6d0ebc3f3565518f6f29d324bb6b280c1626a772bbd12'}
CASES = (("square_two", "square", 1, 2, 38, 4),
         ("square_three", "square", 1, 3, 100, 5),
         ("product_three", "product", 2, 3, 100, 6))


def read_report(raw):
    r = json.loads(raw, object_pairs_hook=unique_object)
    require(isinstance(r, dict) and set(r) == {"schema_version", "frame", "cases",
            "source_sha256", "producer_sha256", "environment", "scope"}, "Invalid top-level fields")
    require(integer(r["schema_version"], "Invalid schema") == 1, "Wrong schema")
    require(r["frame"] == "genus_two_psi_pullbacks_v1", "Wrong claim frame")
    require(r["source_sha256"] == SOURCE_PINS and r["producer_sha256"] == PRODUCER_PINS,
            "Changed source provenance")
    require(r["environment"] == {"sage": "10.9", "admcycles": "1.4"}, "Changed environment")
    require(isinstance(r["scope"], str), "Invalid scope")
    require(isinstance(r["cases"], list) and len(r["cases"]) == 3, "Missing fixed case")
    for c, (name, kind, old, new, size, leading) in zip(r["cases"], CASES):
        require(isinstance(c, dict) and set(c) == {"name", "source_kind", "old_arity", "new_arity",
                "normalization", "coordinates", "leading_column", "support_size"}, "Invalid case fields")
        require(c["name"] == name and c["source_kind"] == kind, "Changed source operation")
        require(integer(c["old_arity"], "Invalid old arity") == old and
                integer(c["new_arity"], "Invalid new arity") == new, "Changed marking operation")
        require(c["normalization"] == "raw_gluing_pushforward", "Changed normalization")
        require(integer(c["leading_column"], "Invalid leading column") == leading, "Changed leading column")
        require(isinstance(c["coordinates"], list) and len(c["coordinates"]) == size, "Wrong frame size")
        values = [rational(x) for x in c["coordinates"]]
        require(integer(c["support_size"], "Invalid support") == sum(x != 0 for x in values),
                "Support metadata disagrees")
    return r


def replay_source(raw):
    r = read_report(raw)
    out = ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
           "Released under Apache 2.0 license as described in the file LICENSE.", "Authors: JMA",
           "-/", "module", "", "public import AxiomaticGW.Tautological.GenusTwoPsiPullbacks", "",
           "/-!", "# Incoming exact coordinates of the fixed genus-two psi pullbacks", "",
           "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
           "The graph operations are held independently in GenusTwoPsiPullbacks.",
           "No incoming vector defines its own requested mathematical operation.", "-/", "",
           "@[expose] public section", "", "namespace AxiomaticGW.GenusTwoPsiPullbacksReplay",
           "open CotangentCombination RelationCertificate GenusTwoPsiPullbacks", "",
           ""]
    for c, (_, _, _, new, size, _) in zip(r["cases"], CASES):
        name = ''.join(w if i == 0 else w.title() for i, w in enumerate(c['name'].split('_')))
        frame = 'GenusTwoPsiProduct' if new == 2 else 'BelorousskiPandharipande'
        out += ["/-- Exact incoming raw coordinates; every nonprimitive correction is retained. -/",
                f"def {name}Claim : Coordinates {size} :=",
                textwrap.fill(rational_vector(c["coordinates"]), width=96,
                              initial_indent="  ", subsequent_indent="    "), "",
                "set_option maxRecDepth 10000 in",
                "/-- Kernel replay compares the vector to the independently computed pullback. -/",
                f"theorem {name}_checked : coordinates {frame}.graph {name} =",
                f"    {name}Claim := by",
                f"  simp only [{frame}.graph, BelorousskiPandharipande.tableGraph,",
                "    DecoratedStableGraph.toDecoration_eq_mk]", "  decide +kernel", "",
                "/-- The accepted vector represents the complete actual graph expression. -/",
                f"theorem {name}_strata : {name}.strata =",
                f"    interpret {frame}.columns {name}Claim := by",
                f"  rw [GenusTwoPsiPullbacks.{name}_strata, {name}_checked]", "",
                "/-- Every nonleading term is a kappa-free boundary with at most one psi factor. -/",
                f"theorem {name}_reduces : ∀ i, i ≠ {c['leading_column']} → {name}Claim i ≠ 0 →",
                f"    0 < ({frame}.graph i).graph.edgeCount ∧",
                f"    ({frame}.graph i).kappaCodimension = 0 ∧",
                f"    ({frame}.graph i).legPsiCodimension +",
                f"      ({frame}.graph i).halfEdgePsiCodimension ≤ 1 := by",
                f"  simp only [{frame}.graph, BelorousskiPandharipande.tableGraph,",
                "    DecoratedStableGraph.toDecoration_eq_mk]", "  decide +kernel", ""]
    out += ["end AxiomaticGW.GenusTwoPsiPullbacksReplay", ""]
    return '\n'.join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = replay_source(args.input.read_bytes())
    if args.check:
        require(args.output.read_text() == source, "Stored replay differs")
    else:
        args.output.write_text(source)


if __name__ == "__main__":
    main()
