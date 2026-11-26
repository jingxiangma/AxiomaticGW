#!/usr/bin/env python3
"""Localize the four canonical genus-two requests at the pullback line on the one-point blowup."""
import hashlib

from export_admcycles_certificate import rational, rational_text, vector
from gkm_genus_two_degree_zero import query_text
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report

KIND = "gkm_localization.f1_plane_line"
LINE = (1, 1)
REQUESTS = {"X0": [], "X1": [
    (LINE, (1, 0, 0, 0), ("H", "pt", "pt", "pt")),
    (LINE, (1, 0, 0), ("pt", "pt", "pt")),
    (LINE, (0, 0, 0, 0), ("pt", "pt", "pt", "pt")),
    (LINE, (1, 0, 0, 0), ("E1", "pt", "pt", "pt")),
], "X2": []}


def emit(raw):
    """Bind each specialized coefficient to its complete incoming descendant query."""
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    incoming = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
                for c in grouped["X1"]}
    cases = [incoming[key] for key in REQUESTS["X1"]]
    return "\n".join([
        "module", "", "public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineReduction", "",
        "/-!", "# Incoming canonical genus-two GKM values at H = E + F on the one-point blowup", "",
        "Report SHA256: " + hashlib.sha256(raw).hexdigest(),
        "The full effective coordinates are one exceptional curve and one fiber.", "-/", "",
        "@[expose] public section", "namespace AxiomaticGW.GKM.F1PlaneLine",
        "open SurfaceGenusTwoBlowupOrder", "",
        "/-- The four incoming requests retain each cotangent power and ordered insertion. -/",
        "def requests : Fin 4 → SurfaceQuery .hirzebruchOne :=",
        "  ![" + ",\n    ".join(map(query_text, cases)) + "]", "",
        "/-- The ordinary specializations of the incoming equivariant localization functions. -/",
        "def values : Fin 4 → ℚ := " + vector([rational_text(rational(c["ordinary"])) for c in cases]),
        "", "/-- Every exchange row is the original full canonical query at H = E + F. -/",
        "theorem coverage (i : Fin 4) : requests i =",
        "    (AxiomaticGW.F1PlaneLine.families i).query AxiomaticGW.F1PlaneLine.line := by",
        "  fin_cases i <;> decide +kernel", "",
        "end AxiomaticGW.GKM.F1PlaneLine", ""])


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
