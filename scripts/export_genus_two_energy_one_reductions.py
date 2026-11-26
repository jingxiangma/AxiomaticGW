#!/usr/bin/env python3
"""Bind the energy-one singleton, marked-equation and primary-point rows to their Lean derivations."""
import argparse
from pathlib import Path

import gkm_bl2_line_one_marking as line_single
import gkm_bl2_line_point_unit_square as line_square
import gkm_genus_two_divisor_pairs as divisor
import gkm_genus_two_energy_one as corpus
import gkm_genus_two_one_marking as single
import gkm_genus_two_positive_pairs as positive
import gkm_genus_two_unit_pairs as unit

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "AxiomaticGW/GKM/Fixtures/GenusTwoEnergyOneReductions.lean"


def witness(target, ns, index, q):
    beta, powers, labels = q
    if beta[-1] == 0 and "pt" in labels:
        return f"verified (.exceptionalPoint (q := requests {index}) (v := 0) (by decide +kernel))"
    if len(labels) == 1:
        if beta[-1] == 0:
            return f"verified (.mixed (GenusTwoOneMarking.{ns}.accepted {single.REQUESTS[target].index(q)}))"
        return f"verified (.mixed (BlowupTwoLineOneMarkingReplay.all_accepted {line_single.REQUESTS[target].index(q)}))"
    for family, t, _, singles in unit.FAMILIES:
        if t == target:
            for j, s in enumerate(singles):
                options = unit.pairs(s)
                if q in options:
                    return f"verified (.unitPair (GenusTwoUnitPairs.{family}.accepted {j} {options.index(q)}).2)"
    for family, t, _, singles, divisors in divisor.FAMILIES:
        if t == target:
            for j, s in enumerate(singles):
                for d, label in enumerate(divisors):
                    opts = divisor.pairs(s, label)
                    if q in opts:
                        name = "all_accepted" if family == "StrictLine" else "accepted"
                        return f"verified (.divisorPair (GenusTwoDivisorPairs.{family}.{name} {j} {d} {opts.index(q)}).2)"
    if q in line_square.REQUESTS[target]:
        return f"verified (.mixed (BlowupTwoLinePointUnitSquare.accepted {line_square.REQUESTS[target].index(q)}))"
    if target == "X2" and beta == (0, 0, 1):
        if labels == ("pt", "pt") and powers == (0, 0):
            return "verified (.mixed BlowupTwoLinePointDivisors.primary)"
        if "pt" in labels:
            point_index = labels.index("pt")
            other = 1 - point_index
            if powers[other] == 1 and powers[point_index] == 0:
                d = ("H", "E1", "E2").index(labels[other])
                return f"verified (.mixed (BlowupTwoLinePointDivisors.value {d} {str(point_index == 0).lower()}))"
    raise ValueError(f"Missing certified reduction for {target} request {q}")


def source():
    lines = ["module", "", "public import AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneClaims",
             "public import AxiomaticGW.GKM.Fixtures.BlowupTwoLineCompletedReplay",
             "public import AxiomaticGW.GKM.Fixtures.BlowupTwoLinePointUnitSquareReplay",
             "public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLinePointDivisors", "",
             "/-! # Singleton, primary-point, string, dilaton and divisor rows at energy one",
             "", "The complementary frame has two insertions of total complex codimension two each",
             "with positive cotangent powers. Every selected row below has its own arithmetic proof.",
             "The binding checks the full request and rational answer against the native frame. -/", "",
             "@[expose] public section", "namespace AxiomaticGW.GKM.GenusTwoEnergyOne",
             "open SurfaceGenusTwoBlowupDescendants", "",
             "private abbrev ProvenRow {X : SurfaceTarget} (i : Fin X.blowups) :=",
             "  {p : SurfaceQuery X × ℚ // CheckedDescendant i p.1 p.2}", "",
             "private def verified {X : SurfaceTarget} {i : Fin X.blowups} {q : SurfaceQuery X} {v : ℚ}",
             "    (h : CheckedDescendant i q v) : ProvenRow i := ⟨(q, v), h⟩", ""]
    for target, ns, surface in (("X1", "OneBlowup", "hirzebruchOne"), ("X2", "TwoBlowups", "blowupTwo")):
        frame = corpus.REQUESTS[target]
        positive_rows = set(positive.REQUESTS[target])
        ids = [idx for idx, q in enumerate(frame) if q not in positive_rows]
        proofs = [witness(target, ns, idx, frame[idx]) for idx in ids]
        lines += [f"namespace {ns}", "",
                  "/-- Original indices of the singleton, primary-point and marked-equation rows. -/",
                  f"def reductionIndex (i : Fin {len(ids)}) : Fin {len(frame)} :=",
                  "  (#[" + ",\n    ".join(", ".join(map(str, ids[j:j+16])) for j in range(0, len(ids), 16))
                  + f"] :\n    Array (Fin {len(frame)}))[i.val]'i.isLt", "",
                  f"private def rows (i : Fin {len(ids)}) : ProvenRow (X := .{surface}) 0 :=",
                  "  (#[" + ",\n    ".join(proofs) + f"] :\n    Array (ProvenRow (X := .{surface}) 0))[i.val]'i.isLt",
                  "", f"private theorem binding : ∀ i : Fin {len(ids)}, (rows i).val =",
                  "    (requests (reductionIndex i), values (reductionIndex i)) := by decide +kernel", "",
                  "/-- Each selected ordinary specialization has an original geometric reconstruction route. -/",
                  f"theorem reductions_accepted (i : Fin {len(ids)}) :",
                  "    CheckedDescendant 0 (requests (reductionIndex i)) (values (reductionIndex i)) := by",
                  "  have h := (rows i).property", "  rwa [binding i] at h", "", f"end {ns}", ""]
    return "\n".join(lines + ["end AxiomaticGW.GKM.GenusTwoEnergyOne", ""])


def selection_source():
    """Partition every original row between the proved marked reductions and the positive-pair packet."""
    lines = ["module", "", "public import AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneReductions",
             "public import AxiomaticGW.GKM.Fixtures.GenusTwoPositivePairClaims", "",
             "/-! # Matching the complete energy-one frame to the two reconstruction cases",
             "", "The selection checks both the ordered query and its independently produced value. -/", "",
             "@[expose] public section", "namespace AxiomaticGW.GKM.GenusTwoEnergyOne", ""]
    for target, ns, surface in (("X1", "OneBlowup", "hirzebruchOne"), ("X2", "TwoBlowups", "blowupTwo")):
        frame, states = corpus.REQUESTS[target], positive.STATES[target]
        classes = [beta for _, t, _, beta in positive.FAMILIES if t == target]
        pos = set(positive.REQUESTS[target])
        reductions = {q: j for j, q in enumerate(q for q in frame if q not in pos)}
        entries = []
        for q in frame:
            if q in reductions:
                entries.append(f".inl {reductions[q]}")
            else:
                b, _, (a, d) = q
                triple = f"{states.index(a)}, {states.index(d)}"
                if target == "X2":
                    triple = f"{classes.index(b)}, " + triple
                entries.append(f".inr ({triple})")
        positive_type = "Fin 3 × Fin 3" if target == "X1" else "Fin 3 × Fin 4 × Fin 4"
        lines.extend([f"namespace {ns}", "", "/-- Reduction index or positive-pair indices for every held row. -/",
                      f"def selection (i : Fin {len(frame)}) : Fin {len(reductions)} ⊕ ({positive_type}) :=",
                      "  (#[" + ",\n    ".join(", ".join(entries[j:j+4]) for j in range(0, len(entries), 4))
                      + f"] :\n    Array (Fin {len(reductions)} ⊕ ({positive_type})))[i.val]'i.isLt", "",
                      "/-- Full request and rational from the selected source. -/",
                      f"def selectedRow : Fin {len(reductions)} ⊕ ({positive_type}) → SurfaceQuery .{surface} × ℚ",
                      "  | .inl j => (requests (reductionIndex j), values (reductionIndex j))"])
        if target == "X1":
            lines += ["  | .inr (a, b) =>",
                      "    (GenusTwoPositivePairs.OneBlowup.requests a b, GenusTwoPositivePairs.OneBlowup.values a b)"]
        else:
            for k, name in enumerate(("ExceptionalOne", "ExceptionalTwo", "StrictLine")):
                lines += [f"  | .inr ({k}, a, b) =>", f"    (GenusTwoPositivePairs.{name}.requests a b,",
                          f"      GenusTwoPositivePairs.{name}.values a b)"]
        lines += ["", "/-- Every full native query and value agree with their source row. -/",
                  f"theorem selection_matches : ∀ i : Fin {len(frame)},",
                  "    selectedRow (selection i) = (requests i, values i) := by decide +kernel",
                  "", f"end {ns}", ""]
    return "\n".join(lines + ["end AxiomaticGW.GKM.GenusTwoEnergyOne", ""])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    opts = parser.parse_args()
    for path, result in ((OUTPUT, source()),
                         (OUTPUT.with_name("GenusTwoEnergyOneSelection.lean"), selection_source())):
        if opts.check:
            if path.read_text() != result:
                parser.exit(1, f"{path.name} differs from its generated derivation.\n")
        else:
            path.write_text(result)
