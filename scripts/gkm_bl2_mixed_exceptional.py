#!/usr/bin/env python3
"""Localize and replay the genus-two few-marking frame in class E₁+E₂ on the two-point blowup."""
from genus_two_few_marking_requests import requests_for
from gkm_regular_fraction_table import ordered_surface_frame
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report

KIND = "gkm_localization.bl2_mixed_exceptional"
REQUESTS = {"X0": [], "X1": [], "X2": [q for q in requests_for("X2") if q[0] == (1, 1, 0)]}


def emit(raw):
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    incoming = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
                for c in grouped["X2"]}
    return ordered_surface_frame(raw, [incoming[q] for q in REQUESTS["X2"]],
                                 lean_target=".blowupTwo", namespace="BlowupTwoMixedExceptional",
                                 title="Genus-two localization in the class E₁+E₂ on the two-point blowup",
                                 generator="gkm_bl2_mixed_exceptional.py")


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
