#!/usr/bin/env python3
"""Localize the genus-two line and exceptional one-marking requests and export their exact claims."""
import hashlib

from export_admcycles_certificate import rational, rational_text, vector
from gkm_report_cli import report_cli
from gkm_genus_two_degree_zero import query_text
from gkm_three_point_descendants import TARGETS, read_report


KIND = "gkm_localization.genus_two_one_marking"


def one_marking(beta, dimension, states):
    """Use complex codimension zero for the unit, two for the point, and one for divisors."""
    return [(beta, (dimension - {"unit": 0, "pt": 2}.get(state, 1),), (state,)) for state in states]


REQUESTS = {
    "X0": one_marking((1,), 5, ("unit", "H", "pt")),
    "X1": one_marking((1, 0), 3, ("unit", "H", "E1", "pt")),
    "X2": [q for beta in ((1, 0, 0), (0, 1, 0))
           for q in one_marking(beta, 3, ("unit", "H", "E1", "E2", "pt"))],
}


def claims(raw):
    """Keep each answer attached to its full request, independent of JSON row order."""
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    lines = ["module", "", "public import AxiomaticGW.Surfaces.Queries", "",
             "/-!", "# GKM genus-two one-marking claims on the line and exceptional curves", "",
             "Report SHA256: " + hashlib.sha256(raw).hexdigest(),
             "Each entry preserves the ordinary specialization of the incoming rational function.",
             "The reconstruction comparisons are proved in separate consumers.", "-/", "",
             "@[expose] public section", "namespace AxiomaticGW.GKM.GenusTwoOneMarking", ""]
    for target, namespace, surface in TARGETS:
        by_key = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
                  for c in grouped[target]}
        cases = [by_key[key] for key in REQUESTS[target]]
        lines += [f"namespace {namespace}", "",
                  "/-- Full ordered requests from the localization report. -/",
                  f"def requests : Fin {len(cases)} → SurfaceQuery .{surface} :=",
                  "  ![" + ",\n    ".join(map(query_text, cases)) + "]", "",
                  "/-- Ordinary values in the same request order. -/",
                  f"def values : Fin {len(cases)} → ℚ :=",
                  "  " + vector([rational_text(rational(c["ordinary"])) for c in cases]), "",
                  f"end {namespace}", ""]
    return "\n".join(lines + ["end AxiomaticGW.GKM.GenusTwoOneMarking", ""])


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=claims)
