#!/usr/bin/env python3
"""Native genus-two reference frames on 2L and the two ruling classes of the two-point blowup."""
import argparse
import sys

from genus_two_few_marking_requests import requests_for
from gkm_regular_fraction_table import ordered_surface_frame
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report


ARITY = {"singletons": 1, "pairs": 2}
CURVES = {(0, 0, 2), (0, 1, 1), (1, 0, 1)}
ELIGIBLE = [q for q in requests_for("X2") if q[0] in CURVES]
REQUESTS = {name: {"X0": [], "X1": [], "X2": [q for q in ELIGIBLE if len(q[1]) == arity]}
            for name, arity in ARITY.items()}


def kind(name):
    return "gkm_localization.bl2_energy_two_positive_plane_" + name


def emit(raw, name):
    requests = REQUESTS[name]
    _, rows = read_report(raw, requests=requests, genus=2, kind=kind(name))
    cases = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c for c in rows["X2"]}
    return ordered_surface_frame(raw, [cases[q] for q in requests["X2"]], lean_target=".blowupTwo",
                                 namespace="BlowupTwoPositivePlaneEnergyTwo" + name.capitalize(),
                                 title=f"Genus-two {name} on 2L and both ruling classes",
                                 generator="gkm_bl2_positive_plane_energy_two.py")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("frame", choices=ARITY)
    name = parser.parse_args(sys.argv[1:2]).frame
    report_cli(__doc__, requests=REQUESTS[name], genus=2, kind=kind(name),
               emit=lambda raw: emit(raw, name), argv=sys.argv[2:])
