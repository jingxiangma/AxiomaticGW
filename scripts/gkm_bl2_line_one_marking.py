#!/usr/bin/env python3
"""Localize the five one-marked descendants in the Bl2 strict-line class."""
import hashlib

from export_admcycles_certificate import rational, rational_text, vector
from gkm_genus_two_degree_zero import query_text
from gkm_genus_two_one_marking import one_marking
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report


KIND = "gkm_localization.bl2_line_one_marking"
REQUESTS = {"X0": [], "X1": [],
            "X2": one_marking((0, 0, 1), 3, ("unit", "H", "E1", "E2", "pt"))}


def emit(raw):
    """Attach each incoming ordinary rational to its complete ordered request."""
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    keyed = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
             for c in grouped["X2"]}
    cases = [keyed[q] for q in REQUESTS["X2"]]
    return "\n".join([
        "module", "", "public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineOneMarking", "",
        "/-!", "# Native GKM one-marked descendants at the Bl2 strict line", "",
        "Report SHA256: " + hashlib.sha256(raw).hexdigest(), "-/", "",
        "@[expose] public section", "namespace AxiomaticGW.GKM.BlowupTwoLineOneMarkingReplay",
        "open BlowupTwoLineBP BlowupTwoLineOneMarking", "",
        "/-- Requests in the order unit, H, E₁, E₂, point. -/",
        "def requests : Fin 5 → SurfaceQuery .blowupTwo :=",
        "  ![" + ",\n    ".join(map(query_text, cases)) + "]", "",
        "/-- Ordinary specialization of each incoming equivariant rational function. -/",
        "def values : Fin 5 → ℚ := " + vector([rational_text(rational(c["ordinary"])) for c in cases]),
        "", "/-- All four high-power native values agree with the original descendant evaluator. -/",
        "theorem high_accepted (j : Fin 4) :",
        "    SurfaceGenusTwoBlowupDescendants.queryValue? 0 (requests j.castSucc) =",
        "      some (values j.castSucc) := by",
        "  have hq : requests j.castSucc = highRequest j := by fin_cases j <;> decide +kernel",
        "  rw [hq, high_descendants]", "  fin_cases j <;> decide +kernel", "",
        "/-- The native point comparison is equivalent to the remaining canonical H value. -/",
        "theorem point_agrees_iff :",
        "    SurfaceGenusTwoBlowupDescendants.queryValue? 0 (requests 4) = some (values 4) ↔",
        "      SurfaceGenusTwoBlowupRecursion.values 0 (line, .hyperplane) = 0 := by",
        "  rw [show requests 4 = pointRequest by decide +kernel, point_descendant]",
        "  exact Option.some_inj", "", "end AxiomaticGW.GKM.BlowupTwoLineOneMarkingReplay", ""])


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
