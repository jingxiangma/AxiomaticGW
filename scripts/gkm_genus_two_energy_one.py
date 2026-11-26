#!/usr/bin/env python3
"""Regenerate the complete fixed genus-two few-marking frame at anticanonical energy one."""
import hashlib

from export_admcycles_certificate import rational, rational_text
from genus_two_few_marking_requests import TARGETS, requests_for
from gkm_genus_two_degree_zero import query_text
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report

KIND = "gkm_localization.genus_two_energy_one_few_markings"
REQUESTS = {
    target: [q for q in requests_for(target)
             if sum(a * w for a, w in zip(q[0], spec["weights"])) == 1]
    for target, spec in TARGETS.items()
}


def emit(raw):
    """Place native answers in benchmark order after checking every full incoming request."""
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    lines = ["module", "", "public import AxiomaticGW.Surfaces.GenusTwoFewMarkings", "",
             "/-! # The full genus-two energy-one localization frame",
             "", "Report SHA256: " + hashlib.sha256(raw).hexdigest(), "-/", "",
             "@[expose] public section", "namespace AxiomaticGW.GKM.GenusTwoEnergyOne", ""]
    for target, ns, surface in (("X1", "OneBlowup", "hirzebruchOne"), ("X2", "TwoBlowups", "blowupTwo")):
        cases = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c for c in grouped[target]}
        rows = [cases[q] for q in REQUESTS[target]]
        size = len(rows)
        lines += [f"namespace {ns}", "", "/-- Full curve and ordered insertions in fixed benchmark order. -/",
                  f"def requests (i : Fin {size}) : SurfaceQuery .{surface} :=",
                  "  (#[" + ",\n    ".join(map(query_text, rows)) + f"] :\n    Array (SurfaceQuery .{surface}))[i.val]'i.isLt",
                  "", "/-- Candidate ordinary values from the native three-target localization interface. -/",
                  f"def values (i : Fin {size}) : ℚ :=",
                  "  (#[" + ",\n    ".join(", ".join(rational_text(rational(c["ordinary"])) for c in rows[j:j+8])
                                          for j in range(0, size, 8)) + "] :\n    Array ℚ)[i.val]'i.isLt",
                  "", f"end {ns}", ""]
    return "\n".join(lines + ["end AxiomaticGW.GKM.GenusTwoEnergyOne", ""])


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
