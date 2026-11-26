#!/usr/bin/env python3
"""Localize and replay the seed-free two-marked divisor benchmark on both blowups."""
import argparse
import sys

from genus_two_few_marking_requests import requests_for
from genus_two_zero_divisor_pairs import accepts
from gkm_regular_fraction_table import ordered_surface_frame
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report


FRAMES = {"X1": (".hirzebruchOne", "F1ZeroDivisorPairs", "F₁"),
          "X2": (".blowupTwo", "BlowupTwoZeroDivisorPairs", "the two-point blowup")}


def kind(target):
    return "gkm_localization.zero_divisor_pairs." + target


def requests(target):
    frame = {"X0": [], "X1": [], "X2": []}
    for beta, powers, labels in requests_for(target):
        query = {"target": target, "genus": 2, "class": beta,
                 "insertions": list(zip(labels, powers))}
        if accepts(query):
            frame[target].append((beta, powers, labels))
    return frame


def emit(raw, target):
    frame = requests(target)
    _, grouped = read_report(raw, requests=frame, genus=2, kind=kind(target))
    incoming = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
                for c in grouped[target]}
    lean_target, namespace, surface = FRAMES[target]
    source = ordered_surface_frame(raw, [incoming[q] for q in frame[target]],
                                   lean_target=lean_target, namespace=namespace,
                                   title="Seed-free genus-two divisor-pair localization on " + surface,
                                   generator="gkm_zero_divisor_pairs.py")
    return source.replace("] : Array (SurfaceQuery", "] :\n    Array (SurfaceQuery")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", choices=FRAMES)
    target = parser.parse_args(sys.argv[1:2]).target
    report_cli(__doc__, requests=requests(target), genus=2, kind=kind(target),
               emit=lambda raw: emit(raw, target), argv=sys.argv[2:])
