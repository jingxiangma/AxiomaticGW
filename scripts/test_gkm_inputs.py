#!/usr/bin/env python3
"""Exercise GKM input checking through its public command-line interface.

Mutated bundles receive a fresh digest, so rejection must come from their
mathematical contents or schema rather than an obsolete checksum. Valid
changes of rational representatives and edge orientation must be accepted.
This tests candidate-data checking, not Lean or geometric soundness.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def put(report, path, value):
    location = report
    for key in path[:-1]:
        location = location[key]
    location[path[-1]] = value


def scale_fraction(report):
    value = report["targets"][0]["euler"][0]
    for part in ["numerator", "denominator"]:
        for term in value[part]:
            term[1][0] *= 7
    value["denominator_nonzero_term"] = copy.deepcopy(value["denominator"][0])


def reverse_edge(report):
    edge = report["targets"][2]["edges"][0]
    edge["source"], edge["target"] = edge["target"], edge["source"]
    edge["weight"] = [-c for c in edge["weight"]]
    for normal in edge["normal_bundles"]:
        normal[0], normal[1] = normal[1], normal[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", nargs="?", type=Path,
                        default=ROOT / "environments/gkm-inputs-osx-arm64.json")
    args = parser.parse_args()
    baseline = json.loads(args.report.read_text())
    cases = [("baseline", True, lambda _: None),
             ("equivalent_rational_representative", True, scale_fraction),
             ("reversed_edge_orientation", True, reverse_edge)]
    mutations = [
        ("boolean_schema", ["schema_version"], True),
        ("boolean_producer_schema", ["source", "schema_version"], True),
        ("boolean_coefficient_degree", ["coefficients", "codimensions", 0], True),
        ("changed_coefficient_encoding", ["coefficients", "rational_encoding"], "float"),
        ("unsupported_cohft_claim", ["cohft", "classes"], {}),
        ("changed_target", ["targets", 0, "target"], "X1"),
        ("changed_fan_ray", ["targets", 0, "rays", 2, 0], -2),
        ("changed_point_cone", ["targets", 0, "points", 0], [0, 2]),
        ("changed_tangent_character", ["targets", 0, "tangent_characters", 0, 0], [1, 1]),
        ("changed_basis_restriction", ["targets", 0, "basis_to_fixedpoint", 0, 0,
                                       "numerator", 0, 1, 0], 2),
        ("changed_inverse_basis", ["targets", 0, "fixedpoint_to_basis", 0, 0,
                                    "numerator", 0, 1, 0], 2),
        ("changed_metric", ["targets", 0, "metric", 0, 2, "numerator", 0, 1, 0], 2),
        ("changed_product", ["targets", 0, "products", 0, 0, 0, "numerator", 0, 1, 0], 2),
        ("changed_c1", ["targets", 0, "c1_coordinates", 1, "numerator", 0, 1, 0], 4),
        ("changed_energy", ["targets", 1, "energy_weights", 1], 1),
        ("changed_curve_transport", ["targets", 2, "curve_to_signed_lattice", 1, 0], -1),
        ("changed_divisor_intersection", ["targets", 1, "divisor_curve_intersections", 1, 3], [1, 1]),
        ("changed_edge_wall", ["targets", 0, "edges", 0, "wall"], [1]),
        ("same_energy_different_exceptional_class", ["targets", 2, "edges", 2, "class"], [0, 1, 0]),
        ("changed_normal_branch", ["targets", 1, "edges", 0, "normal_bundles", 0, 0], 1),
        ("changed_normal_degree", ["targets", 1, "edges", 0, "normal_bundles", 0, 2], 1),
        ("changed_query_class", ["targets", 2, "queries", 2, "class"], [0, 1, 0]),
        ("changed_query_descendant", ["targets", 0, "queries", 1, "insertions", 0, "psi"], 0),
        ("changed_query_label", ["targets", 0, "queries", 0, "insertions", 0, "label"], 1),
        ("changed_query_value", ["targets", 0, "queries", 0, "claimed_value", "numerator", 0, 1, 0], 1),
        ("changed_unstable_arity_flag", ["targets", 2, "queries", 2, "curve_stable"], True),
        ("zero_denominator", ["targets", 0, "euler", 0, "denominator"], []),
        ("incorrect_nonzero_witness", ["targets", 0, "euler", 0, "denominator_nonzero_term"],
         [[0, 0], [2, 1]]),
        ("floating_coefficient", ["targets", 0, "euler", 0, "numerator", 0, 1, 0], 0.5),
        ("negative_rational_denominator", ["targets", 0, "euler", 0, "numerator", 0, 1, 1], -1),
    ]
    for name, path, value in mutations:
        cases.append((name, False, lambda report, p=path, v=value: put(report, p, v)))
    results = []
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-gkm-tests-") as temporary:
        for name, accepted, mutate in cases + [("duplicate_json_key", False, lambda _: None)]:
            print(f"Checking {name}", file=sys.stderr, flush=True)
            report = copy.deepcopy(baseline)
            mutate(report)
            report["targets_sha256"] = hashlib.sha256(json.dumps(
                report["targets"], sort_keys=True, separators=(",", ":")).encode()).hexdigest()
            data = json.dumps(report)
            if name == "duplicate_json_key":
                data = data[:-1] + ',"schema_version":1}'
            path = Path(temporary) / f"{name}.json"
            path.write_text(data)
            result = subprocess.run([sys.executable, str(ROOT / "scripts/check_gkm_inputs.py"),
                                     str(path)], capture_output=True, text=True)
            if (result.returncode == 0) != accepted:
                raise ValueError(f"Unexpected acceptance for {name}: {result.stdout}{result.stderr}")
            if accepted:
                output = json.loads(result.stdout)
                if output["status"] != "passed" or len(output["targets"]) != 3:
                    raise ValueError(f"Missing successful check report for {name}")
            elif "GKM input checks FAILED:" not in result.stderr:
                raise ValueError(f"Checker crashed instead of rejecting {name}: {result.stderr}")
            results.append({"case": name, "expected": "accepted" if accepted else "rejected",
                            "status": "passed"})
    print(json.dumps({"status": "passed", "sage_required": False,
                      "scope": "GKM candidate-data regression tests; no geometric or Lean certificate claim",
                      "input_sha256": hashlib.sha256(args.report.read_bytes()).hexdigest(),
                      "cases": results}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, IndexError) as error:
        print(f"GKM input regression FAILED: {error}", file=sys.stderr)
        raise SystemExit(1)
