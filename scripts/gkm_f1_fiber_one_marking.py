#!/usr/bin/env python3
"""Replay the four genus-two singleton descendants in the fiber class on the one-point blowup."""
import hashlib

from export_admcycles_certificate import rational
from export_gkm_certificate import has_variable_denominator
from genus_two_few_marking_requests import requests_for
from gkm_genus_two_degree_zero import query_text
from gkm_regular_fraction_table import fraction_table
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report

KIND = "gkm_localization.f1_fiber_one_marking"
REQUESTS = {"X0": [], "X1": [q for q in requests_for("X1") if q[0] == (0, 1) and len(q[1]) == 1],
            "X2": []}


def emit(raw):
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    incoming = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
                for c in grouped["X1"]}
    cases = [incoming[q] for q in REQUESTS["X1"]]
    fractions = [(c["equivariant"], rational(c["ordinary"])) for c in cases]
    variable_denominator = any(has_variable_denominator(f) for f, _ in fractions)
    lines = ["module", "", "public import AxiomaticGW.GKM.EquivariantCoefficients",
             "public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberOneMarking",
             *(["public import Mathlib.Tactic.Ring"] if variable_denominator else []), "",
             "/-! # Localization of the four one-marked genus-two fiber descendants on F₁",
             "", "Report SHA256: " + hashlib.sha256(raw).hexdigest(), "-/", "",
             "@[expose] public section", "", "namespace AxiomaticGW.GKM.F1FiberOneMarking",
             "open EquivariantCoefficients", "",
             "/-- Incoming effective classes and ordered descendants. -/",
             "def requests : Fin 4 → SurfaceQuery .hirzebruchOne :=",
             "  ![" + ",\n    ".join(map(query_text, cases)) + "]", "",
             *fraction_table(fractions),
             "/-- The incoming ordinary values, in the held order. -/",
             "abbrev values := FractionTable.constants", "",
             "/-- The full reported two-character functions in the same order. -/",
             "noncomputable abbrev equivariant := FractionTable.fraction", "",
             "/-- Equality holds in the full two-character fraction field. -/",
             "theorem equivariant_eq_ordinary (j : Fin 4) :",
             "    equivariant j = (values j : Coefficient) := FractionTable.fraction_eq_constant j", "",
             "/-- Regular specialization at zero yields each ordinary value. -/",
             "theorem specializes (j : Fin 4) : Specializes (equivariant j) (values j) :=",
             "  FractionTable.specializes j", "",
             "/-- The original reconstructed descendant and native localization agree. -/",
             "theorem accepted (j : Fin 4) : SurfaceGenusTwoBlowupDescendants.queryValue? 0",
             "    (requests j) = some (values j) := by",
             "  have hq : requests j = BlowupF1FiberOneMarking.requests j := by",
             "    fin_cases j <;> decide +kernel",
             "  rw [hq, BlowupF1FiberOneMarking.accepted]",
             "  fin_cases j <;> decide +kernel", "", "end AxiomaticGW.GKM.F1FiberOneMarking", ""]
    return "\n".join(lines)


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
