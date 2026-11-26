#!/usr/bin/env python3
"""Localize genus-two primary divisor pairs in both orders at the fixed line and exceptional classes."""
import hashlib

from export_admcycles_certificate import rational, rational_text, vector
from gkm_bl2_line_one_marking import REQUESTS as LINE
from gkm_genus_two_degree_zero import query_text
from gkm_genus_two_one_marking import REQUESTS as SINGLES
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report


KIND = "gkm_localization.genus_two_divisor_pairs"
FAMILIES = (("Plane", "X0", "plane", SINGLES["X0"], ("H",)),
            ("OneBlowup", "X1", "hirzebruchOne", SINGLES["X1"], ("H", "E1")),
            ("TwoBlowups", "X2", "blowupTwo", SINGLES["X2"], ("H", "E1", "E2")),
            ("StrictLine", "X2", "blowupTwo", LINE["X2"], ("H", "E1", "E2")))


def pairs(single, divisor):
    beta, (power,), (state,) = single
    return [(beta, (0, power), (divisor, state)), (beta, (power, 0), (state, divisor))]


REQUESTS = {target: [] for target in ("X0", "X1", "X2")}
for _, target, _, singletons, divisors in FAMILIES:
    REQUESTS[target].extend(q for s in singletons for d in divisors for q in pairs(s, d))


def emit(raw):
    """Bind every ordinary claim to its actual ordered state/power data and full curve."""
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    lines = ["module", "", "public import AxiomaticGW.Surfaces.Queries", "", "/-!",
             "# Native genus-two divisor-pair claims", "",
             "Report SHA256: " + hashlib.sha256(raw).hexdigest(), "-/", "",
             "@[expose] public section", "namespace AxiomaticGW.GKM.GenusTwoDivisorPairs", ""]
    for family, target, surface, singletons, divisors in FAMILIES:
        keyed = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
                 for c in grouped[target]}
        # The middle index is H then each exceptional basis divisor; the last index is the order.
        rows = [[[keyed[q] for q in pairs(s, d)] for d in divisors] for s in singletons]
        shape = f"Fin {len(singletons)} → Fin {len(divisors)} → Fin 2 → "
        lines.extend([f"namespace {family}", "", "/-- Each complete ordered localization request. -/",
                      f"def requests : {shape}SurfaceQuery .{surface} :=",
                      "  ![" + ",\n    ".join("![" + ",\n      ".join("![" +
                          ",\n        ".join(map(query_text, pair)) + "]" for pair in row) +
                          "]" for row in rows) + "]", "",
                      "/-- Ordinary specialization at both marking orders. -/",
                      f"def values : {shape}ℚ :=",
                      "  ![" + ",\n    ".join(vector([vector([rational_text(rational(c["ordinary"]))
                          for c in pair]) for pair in row]) for row in rows) + "]",
                      "", f"end {family}", ""])
    return "\n".join(lines + ["end AxiomaticGW.GKM.GenusTwoDivisorPairs", ""])


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
