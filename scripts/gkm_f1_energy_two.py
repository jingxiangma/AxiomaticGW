#!/usr/bin/env python3
"""Native exploration and offline replay of genus-two descendants at energy two on F₁."""
import argparse
from dataclasses import dataclass
from functools import cached_property
import sys

from genus_two_few_marking_requests import requests_for
from gkm_regular_fraction_table import ordered_surface_frame
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report


@dataclass(frozen=True)
class Frame:
    slug: str
    namespace: str
    curve: tuple[int, int]
    arity: int
    title: str

    @property
    def kind(self):
        return "gkm_localization." + self.slug

    @cached_property
    def requests(self):
        return {"X0": [], "X1": [q for q in requests_for("X1")
                                 if q[0] == self.curve and len(q[1]) == self.arity], "X2": []}

    def emit(self, raw):
        _, grouped = read_report(raw, requests=self.requests, genus=2, kind=self.kind)
        incoming = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
                    for c in grouped["X1"]}
        return ordered_surface_frame(raw, [incoming[q] for q in self.requests["X1"]],
                                     lean_target=".hirzebruchOne", namespace=self.namespace,
                                     title=self.title, generator="gkm_f1_energy_two.py")


FIBER_PAIRS = Frame("f1_fiber_pairs", "F1FiberPairs", (0, 1), 2,
                    "Two-marked genus-two localization in the fiber class of F₁")
DOUBLE_SINGLETONS = Frame("f1_double_exceptional_one_marking", "F1DoubleExceptionalOneMarking",
                          (2, 0), 1, "One-marked genus-two localization in twice the exceptional class of F₁")
DOUBLE_PAIRS = Frame("f1_double_exceptional_pairs", "F1DoubleExceptionalPairs", (2, 0), 2,
                     "Two-marked genus-two localization in twice the exceptional class of F₁")
FRAMES = {"fiber-pairs": FIBER_PAIRS, "double-singletons": DOUBLE_SINGLETONS, "double-pairs": DOUBLE_PAIRS}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("frame", choices=FRAMES)
    frame = FRAMES[parser.parse_args(sys.argv[1:2]).frame]
    report_cli(frame.title, requests=frame.requests, genus=2, kind=frame.kind,
               emit=frame.emit, argv=sys.argv[2:])
