#!/usr/bin/env python3
"""Localize the P, N and K states on the F1 fiber and emit their Lean comparisons."""
import hashlib

from export_admcycles_certificate import rational, rational_text, vector
from gkm_genus_two_degree_zero import query_text
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report

KIND = "gkm_localization.f1_fiber_remaining"
FIBER = (0, 1)
REQUESTS = {"X0": [], "X1": [(FIBER, (1, 0), ("pt", "pt")),
                              (FIBER, (0, 0, 0), ("pt", "pt", "pt")),
                              (FIBER, (1, 0, 0), ("E1", "pt", "pt"))], "X2": []}


def emit(raw):
    """Retain each incoming ordinary value paired with its original complete query."""
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    by_request = {(tuple(case["class"]), tuple(case["powers"]), tuple(case["labels"])): case
                  for case in grouped["X1"]}
    cases = [by_request[key] for key in REQUESTS["X1"]]
    return "\n".join([
        "module", "", "public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberTable", "",
        "/-!", "# Three incoming genus-two queries on the F1 fiber", "",
        "Report SHA256: " + hashlib.sha256(raw).hexdigest(),
        "The original canonical reconstruction binds each exact request and ordinary value.",
        "The geometric interpretation uses the original BP/L24 equations and finite seeds.",
        "-/", "", "@[expose] public section", "",
        "namespace AxiomaticGW.GKM.BlowupF1FiberRemainingReplay",
        "open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder BlowupF1FiberHReduction", "",
        "/-- Incoming genus, full curve and ordered labels with their cotangent powers. -/",
        "def requests : Fin 3 → SurfaceQuery .hirzebruchOne :=",
        "  ![" + ",\n    ".join(map(query_text, cases)) + "]", "",
        "/-- Ordinary specialization of each incoming rational function. -/",
        "def values : Fin 3 → ℚ := " + vector([rational_text(rational(c["ordinary"])) for c in cases]),
        "", "/-- The independently specified P, N and K canonical families. -/",
        "def families : Fin 3 → Family target := ![.point, .primary, .exceptional 0]", "",
        "/-- Each request matches its canonical family at the full fiber class. -/",
        "theorem coverage (i : Fin 3) : requests i = (families i).query fiber := by",
        "  fin_cases i <;> decide +kernel", "",
        "/-- The checked finite reconstruction supplies the ordinary value of each request. -/",
        "theorem accepted (i : Fin 3) :",
        "    canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0) (.inr (requests i)) =",
        "      values i := by",
        "  rw [coverage, canonicalValuation_query, BlowupF1FiberTable.fiber_values]",
        "  fin_cases i <;> norm_num [values]", "", "end AxiomaticGW.GKM.BlowupF1FiberRemainingReplay", ""])


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
