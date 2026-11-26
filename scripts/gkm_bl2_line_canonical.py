#!/usr/bin/env python3
"""Localize the five canonical genus-two requests at the strict two-point line."""
import hashlib

from export_admcycles_certificate import rational, rational_text, vector
from gkm_genus_two_degree_zero import query_text
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report

KIND = "gkm_localization.bl2_line_canonical"
LINE = (0, 0, 1)
REQUESTS = {"X0": [], "X1": [], "X2": [
    (LINE, (1, 0), ("H", "pt")),
    (LINE, (1,), ("pt",)),
    (LINE, (0, 0), ("pt", "pt")),
    (LINE, (1, 0), ("E1", "pt")),
    (LINE, (1, 0), ("E2", "pt")),
]}


def emit(raw):
    """Bind each specialized coefficient to its complete incoming descendant query."""
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    incoming = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
                for c in grouped["X2"]}
    cases = [incoming[key] for key in REQUESTS["X2"]]
    return "\n".join([
        "module", "", "public import AxiomaticGW.Surfaces.GenusTwoBlowupOrder", "",
        "/-!", "# Incoming genus-two GKM values on the strict two-point line", "",
        "Report SHA256: " + hashlib.sha256(raw).hexdigest(),
        "The full effective basis is E₁, E₂, H − E₁ − E₂.", "-/", "",
        "@[expose] public section", "namespace AxiomaticGW.GKM.BlowupTwoLineCanonical",
        "open SurfaceGenusTwoBlowupOrder", "",
        "/-- The five incoming requests retain each cotangent power and ordered insertion. -/",
        "def requests : Fin 5 → SurfaceQuery .blowupTwo :=",
        "  ![" + ",\n    ".join(map(query_text, cases)) + "]", "",
        "/-- The ordinary specializations of the incoming equivariant localization functions. -/",
        "def values : Fin 5 → ℚ := " + vector([rational_text(rational(c["ordinary"])) for c in cases]),
        "", "/-- Canonical families in the order of the request frame. -/",
        "def families : Fin 5 → Family .blowupTwo :=",
        "  ![.hyperplane, .point, .primary, .exceptional 0, .exceptional 1]", "",
        "/-- Every exchange row matches its full canonical query at the specified curve. -/",
        "theorem coverage (i : Fin 5) : requests i = (families i).query ![0, 0, 1] := by",
        "  fin_cases i <;> decide +kernel", "",
        "end AxiomaticGW.GKM.BlowupTwoLineCanonical", ""])


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
