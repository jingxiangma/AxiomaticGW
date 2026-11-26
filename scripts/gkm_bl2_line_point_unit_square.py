#!/usr/bin/env python3
"""Localize and replay the strict-line primary-point and cotangent-square unit in both orders."""
import hashlib

from export_admcycles_certificate import rational, rational_text, vector
from gkm_genus_two_degree_zero import query_text
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report


KIND = "gkm_localization.bl2_line_point_unit_square"
LINE = (0, 0, 1)
REQUESTS = {"X0": [], "X1": [],
            "X2": [(LINE, (0, 2), ("pt", "unit")), (LINE, (2, 0), ("unit", "pt"))]}


def emit(raw):
    """Link each exact ordered producer claim to the original bounded mixed evaluator."""
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    keyed = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c for c in grouped["X2"]}
    rows = [keyed[q] for q in REQUESTS["X2"]]
    return "\n".join([
        "module", "", "public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Assembly",
        "public import AxiomaticGW.Surfaces.GenusTwoBlowupQueryCertificate", "", "/-!",
        "# The primary point and the second descendant of the unit on the strict line", "",
        "Report SHA256: " + hashlib.sha256(raw).hexdigest(),
        "The full mixed transfer and its pulled-back square are evaluated with the certified",
        "energy-one canonical table, separately for both ordered requests.", "-/", "",
        "@[expose] public section", "namespace AxiomaticGW.GKM.BlowupTwoLinePointUnitSquare",
        "open SurfaceGenusTwoBlowupDescendants BlowupTwoLineTable", "",
        "/-- The native requests retain both marking orders and all strict-line coordinates. -/",
        "def requests : Fin 2 → SurfaceQuery .blowupTwo :=",
        "  ![" + ",\n    ".join(map(query_text, rows)) + "]", "",
        "/-- Ordinary specialization in each order. -/",
        "def values : Fin 2 → ℚ := " + vector([rational_text(rational(c["ordinary"])) for c in rows]), "",
        "set_option maxRecDepth 65536", "", "set_option maxHeartbeats 1600000 in",
        "-- Each complete mixed expansion includes the universal-curve pullback of the square.",
        "/-- Both ordinary native values agree with the original genus-two descendant evaluator. -/",
        "theorem accepted (o : Fin 2) : queryValue? 0 (requests o) = some (values o) := by",
        "  have he : SurfaceTarget.blowupTwo.effective.energy (requests o).beta ≤ 1 := by",
        "    fin_cases o <;> decide +kernel",
        "  rw [← queryValueWith?_eq 0 1 (candidate 0) BlowupTwoLineTable.accepted _ he]",
        "  fin_cases o <;> decide +kernel", "",
        "end AxiomaticGW.GKM.BlowupTwoLinePointUnitSquare", ""])


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
