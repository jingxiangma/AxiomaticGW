#!/usr/bin/env python3
"""Localize ordered two-marked string and dilaton descendants over certified blowup singletons."""
import hashlib

from export_admcycles_certificate import rational, rational_text, vector
from gkm_bl2_line_one_marking import REQUESTS as LINE
from gkm_genus_two_degree_zero import query_text
from gkm_genus_two_one_marking import REQUESTS as EXCEPTIONAL
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report


KIND = "gkm_localization.genus_two_unit_pairs"
FAMILIES = (("OneBlowup", "X1", "hirzebruchOne", EXCEPTIONAL["X1"]),
            ("TwoBlowups", "X2", "blowupTwo", EXCEPTIONAL["X2"]),
            ("StrictLine", "X2", "blowupTwo", LINE["X2"][:4]),
            ("StrictLinePoint", "X2", "blowupTwo", LINE["X2"][4:]))


def pairs(single):
    beta, (power,), (label,) = single
    return [(beta, powers, labels) for unit, other in ((0, power + 1), (1, power))
            for powers, labels in (((unit, other), ("unit", label)),
                                   ((other, unit), (label, "unit")))]


REQUESTS = {target: [] for target in ("X0", "X1", "X2")}
for _, target, _, singletons in FAMILIES:
    REQUESTS[target].extend(q for singleton in singletons for q in pairs(singleton))


def emit(raw):
    """Record all original marking orders and values independently of source row order."""
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    lines = ["module", "", "public import AxiomaticGW.Surfaces.Queries", "", "/-!",
             "# Genus-two two-marked unit claims from the pinned GKM producer", "",
             "Report SHA256: " + hashlib.sha256(raw).hexdigest(), "-/", "",
             "@[expose] public section", "namespace AxiomaticGW.GKM.GenusTwoUnitPairs", ""]
    for family, target, surface, singletons in FAMILIES:
        keyed = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
                 for c in grouped[target]}
        rows = [[keyed[q] for q in pairs(s)] for s in singletons]
        lines.extend([f"namespace {family}", "",
                      "/-- Ordered requests in string-first, string-last, dilaton-first, dilaton-last order. -/",
                      f"def requests : Fin {len(rows)} → Fin 4 → SurfaceQuery .{surface} :=",
                      "  ![" + ",\n    ".join("![" + ",\n      ".join(map(query_text, row))
                                            + "]" for row in rows) + "]", "",
                      "/-- Ordinary specializations in the same frame. -/",
                      f"def values : Fin {len(rows)} → Fin 4 → ℚ :=",
                      "  ![" + ",\n    ".join(vector([rational_text(rational(c["ordinary"]))
                                                 for c in row]) for row in rows) + "]",
                      "", f"end {family}", ""])
    return "\n".join(lines + ["end AxiomaticGW.GKM.GenusTwoUnitPairs", ""])


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
