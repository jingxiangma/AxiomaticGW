#!/usr/bin/env python3
"""Export exact surface equation candidates against independently held Lean requests.

The source is the pinned Sage degree-zero exploration report. Successful file
generation is not acceptance: Lean must check the complete graph expansion.
No Sage, network lookup, numerical evaluation, or digest proves acceptance.
"""

import argparse
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from explore_surface_getzler import curve_assignments
from explore_surface_reduction import reduce_key
from explore_surface_degree_zero import constant_value


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "environments/surface-degree-zero-exploration.json"
SOURCE_SHA256 = "0fd1d642cad8cd1f4350c283b352238d2a5c06dc1342818d34b9164dd3efeb68"
FRAME = ROOT / "environments/getzler-candidate-osx-arm64.json"
FRAME_SHA256 = "ccd8a8f941e9d2d503ec91e29b2be527bf0c91ce111599e6ec56118f6994ecb7"
HELPER_SHA256 = {
    "explore_surface_getzler.py": "f34f5288ef6b3a3b0a5417038f3d5e6b3f3f24c683c359431e7f0e39816fdd37",
    "explore_surface_reduction.py": "a0e96453cb0063df446ae9f3ddd6416e6308a8466a0d52d1a6316fb4fcf8e5e4",
    "explore_surface_degree_zero.py": "65afcfe6fa0017a6bc5f1f1627a18c17d144b20ec4566d6e0283b972d122ba61",
}
REQUESTS = (
    ("P2", (1,), 1, "plane", "planeLine"),
    ("F1", (1, 1), 1, "hirzebruchOne", "hirzebruchLine"),
    ("Bl2P2", (1, 1, 1), 1, "blowupTwo", "blowupLine"),
    ("Bl2P2", (1, 1, 0), 0, "blowupTwo", "exceptionalSum"),
)


def lean_curve(curve):
    if not curve or any(type(c) is not int or c < 0 for c in curve):
        raise ValueError("Expected full nonnegative integral curve coordinates")
    return "![" + ", ".join(map(str, curve)) + "]"


def point_variable(target, raw):
    tag, genus, curve, insertions = raw
    if tag != "query" or type(genus) is not int or genus < 0:
        raise ValueError("This fixed exporter expects numerical point-query variables")
    if len(curve) != {"plane": 1, "hirzebruchOne": 2, "blowupTwo": 3}[target]:
        raise ValueError("The full curve coordinate count does not match the target")
    if any(tuple(insertion) != (2, 0) or any(type(n) is not int for n in insertion)
           for insertion in insertions):
        raise ValueError("A non-point insertion or nonzero power must not be erased")
    return f".inr (SurfaceQuery.points .{target} {genus} {lean_curve(curve)} {len(insertions)})"


def expanded_columns(frame, target, curve, extra, original_labels=(1, 1, 1, 1), *, expected_columns=33):
    """Uncollected witness; Lean checks its multiset equality with the held frame.

    The incidence expansion and component rules are exploration code only.
    Keeping separate contributions avoids recomputing the full graph expansion
    once per distinct coefficient during kernel replay.
    """
    blowups = len(curve) - 1
    dual = (2, 1, 0) + tuple(range(3, 3 + blowups))
    inverse = (1, 1, 1) + (-1,) * blowups
    if len(original_labels) != 4 or any(
            type(s) is not int or not 0 <= s < len(dual) for s in original_labels):
        raise ValueError("Expected four basis labels for the specified surface")
    columns = []
    if type(expected_columns) is not int or expected_columns <= 0:
        raise ValueError("Expected a positive integral column count")
    if len(frame["graphs"]) != expected_columns or len(frame["requested"]) != expected_columns:
        raise ValueError(f"The original {expected_columns}-column frame changed")
    for graph, ratio in zip(frame["graphs"], frame["requested"]):
        output = []
        vertices = len(graph["genus"])
        classes = tuple(curve_assignments(curve, vertices))
        for placement in product(range(vertices), repeat=extra):
            markings = graph["leg_vertices"] + list(placement)
            for states in product(range(len(dual)), repeat=len(graph["endpoints"])):
                insertions = [[] for _ in range(vertices)]
                for label, vertex in enumerate(markings):
                    insertions[vertex].append((original_labels[label] if label < 4 else 2, 0))
                weight = Fraction(*ratio)
                for state, (left, right) in zip(states, graph["endpoints"]):
                    insertions[left].append((state, 0))
                    insertions[right].append((dual[state], 0))
                    weight *= inverse[state]
                for assignment in classes:
                    coefficient, monomial = weight, []
                    for v in range(vertices):
                        key = (graph["genus"][v], assignment[v], tuple(sorted(insertions[v])))
                        reduced, _ = reduce_key(target, key, Fraction)
                        if reduced is None:
                            break
                        factor, variable = reduced
                        coefficient *= factor
                        constant = constant_value(variable, Fraction)
                        if constant is None:
                            monomial.append(variable)
                        else:
                            coefficient *= constant
                        if not coefficient:
                            break
                    else:
                        output.append([sorted(monomial), [coefficient.numerator, coefficient.denominator]])
        columns.append(output)
    return columns


def expanded_terms(frame, target, curve, extra, original_labels=(1, 1, 1, 1)):
    return [term for column in expanded_columns(frame, target, curve, extra, original_labels)
            for term in column]


def lean_terms(target, terms):
    if not terms:
        return f"(0 : RationalTerms (Variable .{target}))"
    output = []
    for monomial, (numerator, denominator) in terms:
        if type(numerator) is not int or type(denominator) is not int or denominator <= 0:
            raise ValueError("Expected an exact rational coefficient")
        variables = ",\n        ".join(point_variable(target, v) for v in monomial)
        output.append(f"(({numerator} / {denominator} : ℚ),\n"
                      f"      (↑([\n        {variables}]\n"
                      f"        : List (Variable .{target})) : Multiset (Variable .{target})))")
    return "↑[\n    " + ",\n    ".join(output) + "]"


def export():
    for name, expected in HELPER_SHA256.items():
        if hashlib.sha256((ROOT / "scripts" / name).read_bytes()).hexdigest() != expected:
            raise ValueError(f"The exploration helper changed: {name}")
    source = SOURCE.read_bytes()
    if hashlib.sha256(source).hexdigest() != SOURCE_SHA256:
        raise ValueError("The pinned Sage exploration report changed")
    report = json.loads(source)
    frame_data = FRAME.read_bytes()
    if hashlib.sha256(frame_data).hexdigest() != FRAME_SHA256:
        raise ValueError("The original Getzler frame changed")
    frame = json.loads(frame_data)
    if len(report["cases"]) != len(REQUESTS):
        raise ValueError("The fixed request set changed")
    lines = ["-- Generated by scripts/export_surface_equations.py.",
             "-- Candidate coefficients only; each proof checks the independent graph request.",
             "module", "", "public import AxiomaticGW.Surfaces.Fixtures.GetzlerFrames", "",
             "@[expose] public section", "",
             "namespace AxiomaticGW.SurfaceGetzlerReplay", "",
             "open SurfacePolynomialReduction", ""]
    for case, (target, curve, extra, lean_target, name) in zip(report["cases"], REQUESTS):
        if (case["target"], tuple(case["curve"]), case["extra_markings"]) != (target, curve, extra):
            raise ValueError("Candidate is not bound to the expected fixed request")
        columns = expanded_columns(frame, target, curve, extra)
        expanded = ",\n    ".join(lean_terms(lean_target, column) for column in columns)
        lines.append(f"-- Exact witnesses for all 33 columns: {sum(map(len, columns))} contributions.\n"
                     f"private def {name}Expanded :\n"
                     f"    Fin 33 → RationalTerms (Variable .{lean_target}) :=\n"
                     f"  ![{expanded}]\n")
        lines.append("set_option maxHeartbeats 0 in\n"
                     "-- The finite graph calculation needs a larger kernel-reduction budget.\n"
                     "set_option maxRecDepth 65536 in\n"
                     f"private theorem {name}_expanded :\n"
                     f"    SurfaceGetzlerFrames.{name} = ∑ i, {name}Expanded i := by\n"
                     f"  unfold SurfaceGetzlerFrames.{name} GetzlerGraphs.primaryTerms\n"
                     f"    GetzlerGraphs.surfaceTerms\n"
                     f"  apply Finset.sum_congr rfl\n"
                     f"  intro i _\n"
                     f"  fin_cases i <;> decide +kernel\n")
        lines.append(f"/-- Candidate terms for the independently held `{name}` graph request. -/\n"
                     f"def {name} : RationalTerms (Variable .{lean_target}) :=\n"
                     f"  {lean_terms(lean_target, case['terms'])}\n")
        lines.append("set_option maxHeartbeats 0 in\n"
                     "-- Collect all finite column contributions by exact coefficient comparison.\n"
                     "set_option maxRecDepth 65536 in\n"
                     f"/-- Kernel equality with the complete reduced graph expansion. -/\n"
                     f"theorem {name}_accepted :\n"
                     f"    RationalTerms.Equivalent SurfaceGetzlerFrames.{name} {name} := by\n"
                     f"  rw [{name}_expanded]\n"
                     f"  decide +kernel\n")
    lines.append("end AxiomaticGW.SurfaceGetzlerReplay\n")
    return "\n".join(lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(export())
