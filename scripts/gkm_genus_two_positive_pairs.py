#!/usr/bin/env python3
"""Localize the genus-two two-marked weight-two insertions in all four energy-one classes."""
import hashlib
from itertools import product

from export_admcycles_certificate import rational, rational_text, vector
from gkm_genus_two_degree_zero import query_text
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report


KIND = "gkm_localization.genus_two_positive_pairs"
FAMILIES = (("OneBlowup", "X1", "hirzebruchOne", (1, 0)),
            ("ExceptionalOne", "X2", "blowupTwo", (1, 0, 0)),
            ("ExceptionalTwo", "X2", "blowupTwo", (0, 1, 0)),
            ("StrictLine", "X2", "blowupTwo", (0, 0, 1)))
STATES = {"X1": ("unit", "H", "E1"), "X2": ("unit", "H", "E1", "E2")}


def pair(beta, a, b):
    return (beta, (2 if a == "unit" else 1, 2 if b == "unit" else 1), (a, b))


REQUESTS = {x: [] for x in ("X0", "X1", "X2")}
for _, target, _, beta in FAMILIES:
    REQUESTS[target].extend(pair(beta, a, b) for a, b in product(STATES[target], repeat=2))


def emit(raw):
    """Bind both powers, both ordered labels, and every effective coordinate to each claim."""
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    lines = ["module", "", "public import AxiomaticGW.Surfaces.Queries", "", "/-!",
             "# Native two-marked positive-cotangent claims in anticanonical degree one", "",
             "Report SHA256: " + hashlib.sha256(raw).hexdigest(), "-/", "",
             "@[expose] public section", "namespace AxiomaticGW.GKM.GenusTwoPositivePairs", ""]
    for family, target, surface, beta in FAMILIES:
        keyed = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c for c in grouped[target]}
        states = STATES[target]
        rows = [[keyed[pair(beta, a, b)] for b in states] for a in states]
        shape = f"Fin {len(states)} → Fin {len(states)} → "
        lines.extend([f"namespace {family}", "", "/-- Ordered localization requests. -/",
                      f"def requests : {shape}SurfaceQuery .{surface} :=",
                      "  ![" + ",\n    ".join("![" + ",\n      ".join(map(query_text, row)) + "]"
                                             for row in rows) + "]", "",
                      "/-- Ordinary specialization in the same basis and marking order. -/",
                      f"def values : {shape}ℚ :=",
                      "  ![" + ",\n    ".join(vector([rational_text(rational(c["ordinary"]))
                                                   for c in row]) for row in rows) + "]", "",
                      f"end {family}", ""])
    return "\n".join(lines + ["end AxiomaticGW.GKM.GenusTwoPositivePairs", ""])


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
