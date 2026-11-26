#!/usr/bin/env python3
"""Localize every dimension-matched genus-two request with at most two marks in 2E₁ and 2E₂."""
from genus_two_few_marking_requests import requests_for
from gkm_f1_energy_two import DOUBLE_PAIRS, DOUBLE_SINGLETONS
from gkm_regular_fraction_table import indexed_array, ordered_surface_frame
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report


KIND = "gkm_localization.bl2_double_exceptional_few_markings"
NAMESPACE = "BlowupTwoDoubleExceptionalFewMarkings"
CURVES = ((2, 0, 0), (0, 2, 0))
REQUESTS = {"X0": [], "X1": [], "X2": [q for q in requests_for("X2") if q[0] in CURVES]}


def f1_index(request):
    """Offer the corresponding ordered F₁ row, or zero for a foreign exceptional insertion."""
    curve, powers, labels = request
    axis = CURVES.index(curve)
    if ("E2", "E1")[axis] in labels:
        return "none"
    projected = ((2, 0), powers, tuple("E1" if label == "E2" else label for label in labels))
    source, tag = (DOUBLE_SINGLETONS, "inl") if len(labels) == 1 else (DOUBLE_PAIRS, "inr")
    return f"some (.{tag} {source.requests['X1'].index(projected)})"


def emit(raw):
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    incoming = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c for c in grouped["X2"]}
    order = REQUESTS["X2"]
    source = ordered_surface_frame(raw, [incoming[q] for q in order], lean_target=".blowupTwo",
                                  namespace=NAMESPACE, title="Genus-two full fields in both double exceptional classes",
                                  generator="gkm_bl2_double_exceptional_few_markings.py")
    end = f"end AxiomaticGW.GKM.{NAMESPACE}\n"
    indices = indexed_array([f1_index(q) for q in order], "Option (Fin 4 ⊕ Fin 64)", 5)
    indices = indices.replace("] : Array", "] :\n    Array")
    return source.removesuffix(end) + (
        "/-- Proposed F₁ singleton or ordered pair index. A foreign exceptional marking has no index. -/\n"
        f"def counterpart (i : Fin {len(order)}) : Option (Fin 4 ⊕ Fin 64) :=\n{indices}\n\n{end}")


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
