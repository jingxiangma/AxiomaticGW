#!/usr/bin/env python3
"""Regenerate the structural certificates for the Bl₂ strict-transform line L24 sum."""
import argparse
from pathlib import Path
import re

from export_f1_root_relabel_transfers import (
    CLAIMS, SOURCE, CoordinateParser, analyze, coordinate, declaration, equiv,
)


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "AxiomaticGW/Surfaces/Fixtures/BlowupTwoLineL24"
UPPER = ROOT / "AxiomaticGW/Surfaces/GenusTwoBlowupHUniform.lean"
MODULE = "AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24"
NAMESPACE = "AxiomaticGW.BlowupTwoLineH.Frame"
HEADER = """\
/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

"""


def partition():
    """Select lower-genus rows from the original weights and checked genus-two frame."""
    claims = (ROOT / CLAIMS).read_text()
    weights = CoordinateParser(declaration(claims, "fullClaim")).parse()
    upper = re.search(r"def genusTwoFrame : Finset \(Fin 815\) :=\s*\{([\d,\s]+)\}",
                      UPPER.read_text())
    if upper is None:
        raise ValueError("Unrecognized genus-two frame")
    genus_two = {int(index) for index in upper.group(1).split(",")}
    rows = []
    for index in range(815):
        w = coordinate(weights, index)
        rows.append(dict(held_index=index, coefficient=[w.numerator, w.denominator],
                         evaluated=bool(w) and index not in genus_two))
    records, classes, _ = analyze((ROOT / SOURCE).read_text(), claims, {"rows": rows})
    return records, classes


def representatives(groups):
    selected = [group[0] for group in groups]
    result = HEADER + f"""public import {MODULE}.Candidates

/-! # Checked Bl₂ line graph representatives, indices {selected[0]} through {selected[-1]}

Every equality evaluates the complete weighted contraction at the specified
original index, including all intermediate node labels and curve splittings.
-/

@[expose] public section
namespace {NAMESPACE}
set_option Elab.async false
set_option maxRecDepth 65536

"""
    for i in selected:
        result += f"theorem checked{i} : cachedWeighted {i} = candidate {i} := by decide +kernel\n\n"
    return result + f"end {NAMESPACE}\n"


def transports(records, groups):
    result = HEADER + f"""public import {MODULE}.Transfer

/-! # Outer-marking transports for the Bl₂ strict-line contraction

Each proof compares the original decorated graph before the two external
permutations. The three equal exceptional insertions have identical
pullbacks wherever a representative is reused.
-/

@[expose] public section
namespace {NAMESPACE}
open GluingExpression
set_option maxRecDepth 20000

"""
    for group in groups:
        if len(group) == 1:
            continue
        i = group[0]
        expr = f"L24Gluing.term{i}.expression"
        core = expr if records[i]["outer"] is None else f"(underlying {expr}).2.2"
        result += f"private abbrev core{i} : GluingExpression 2 (Fin 4) :=\n  {core}\n\n"
        for j in group[1:]:
            result += f"""theorem same{j} : unweighted {i} = unweighted {j} :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core{i} L24Gluing.term{i}.decoration L24Gluing.term{i}.labels
    {equiv(records[i])} {equiv(records[j])} shifted 0 labels (by decide +kernel)

"""
    return result + f"end {NAMESPACE}\n"


def dispatch(records, groups):
    """Construct the finite coverage using only original indices and their identifications."""
    rep = {j: group[0] for group in groups for j in group}
    blocks = []
    for b in range(26):
        lines = [f"private theorem checkedBlock{b} (i : Fin 32) : atIndex (32 * {b} + i.val) := by",
                 "  fin_cases i <;> intro h"]
        for j in range(32 * b, 32 * (b + 1)):
            if j >= len(records):
                proof = f"exact False.elim ((by decide : ¬ {j} < 815) h)"
            elif j not in rep:
                proof = f"exact inactive {j} (by decide +kernel)"
            elif rep[j] == j:
                proof = f"exact checked{j}"
            else:
                i = rep[j]
                proof = f"exact transfer {i} {j} same{j} checked{i} (by decide +kernel)"
            lines.append("  · " + proof)
        blocks.append("\n".join(lines))
    return "\n\n".join(blocks) + "\n\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="report any stale certificate")
    args = parser.parse_args()
    records, groups = partition()
    outputs = {}
    for batch, start in enumerate(range(0, len(groups), 20)):
        selected = groups[start:start + 20]
        outputs[OUT / f"Representatives{batch:02}.lean"] = representatives(selected)
        outputs[OUT / f"Transports{batch:02}.lean"] = transports(records, selected)
    assembly = OUT / "Assembly.lean"
    old = assembly.read_text()
    begin = old.index("private theorem checkedBlock0")
    end = old.index("/-- Numerically certified contraction")
    outputs[assembly] = old[:begin] + dispatch(records, groups) + old[end:]
    for path, content in outputs.items():
        if args.check:
            if not path.exists() or path.read_text() != content:
                raise SystemExit(f"Stale certificate: {path}")
        else:
            path.write_text(content)


if __name__ == "__main__":
    main()
