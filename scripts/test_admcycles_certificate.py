#!/usr/bin/env python3
"""Test the fixed certificate exchange with Lean alone, without Sage.

Every kernel case uses the same compiled graph frame, relation rows, and
requested expression. Digests are recomputed after JSON mutations, so the
negative cases exercise mathematical field checks rather than hash checks.
This verifies the diagnostic fixture's exchange; it does not prove geometric
FZ vanishing or the full R4 reconstruction acceptance gate.
"""

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
EXPORTER = ROOT / "scripts" / "export_admcycles_certificate.py"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                    separators=(",", ":")).encode()).hexdigest()


def updated_report(report, change):
    result = copy.deepcopy(report)
    change(result)
    result["raw_coordinate_sha256"] = digest(result["coordinates"])
    result["exact_arithmetic_sha256"] = digest(result["arithmetic"])
    return result


def set_field(section, key, value):
    return lambda report: report[section].__setitem__(key, value)


def change_entry(section, key, row, column, value):
    return lambda report: report[section][key][row].__setitem__(column, value)


def change_graph(report):
    # Replace the loop-plus-bridge graph by a different valid genus-two
    # codimension-two graph. Parsing succeeds; its fixed semantic slot fails.
    graph = copy.deepcopy(report["coordinates"]["graphs"][7])
    graph["index"] = 6
    report["coordinates"]["graphs"][6] = graph


def swap_loop_branches(report):
    # X^2 is the second loop branch's psi exponent, not twice that exponent.
    report["coordinates"]["graphs"][5]["matrix_polynomials"][1][1] = [
        [[0], 2], [[2], 1],
    ]


def change_label(report):
    report["coordinates"]["graphs"][2]["matrix_polynomials"][0][1] = [[[0], 1]]


def change_witness(report):
    values = report["arithmetic"]["row_combination_witness"]
    value = Fraction(*values[0]) + 1
    values[0] = [value.numerator, value.denominator]


def swap_generator_references(report):
    values = report["arithmetic"]["fz_rows_monomial"]
    values[0], values[3] = values[3], values[0]


def run_case(directory, name, report, *, parse_ok=True, kernel_ok=False,
             source_change=None, raw_text=None):
    print(f"Checking {name}", file=sys.stderr, flush=True)
    path = directory / f"{name}.json"
    path.write_text(raw_text if raw_text is not None else json.dumps(report))
    exported = subprocess.run([sys.executable, str(EXPORTER), str(path)], cwd=ROOT,
                              capture_output=True, text=True)
    require((exported.returncode == 0) == parse_ok,
            f"{name}: unexpected exporter outcome: {exported.stderr}")
    if not parse_ok:
        require(not exported.stdout, f"{name}: failed parser emitted partial Lean data")
        return {"case": name, "parser": "rejected"}
    source = exported.stdout
    if source_change is not None:
        source = source_change(source)
    lean_path = directory / f"{name}.lean"
    lean_path.write_text(source)
    checked = subprocess.run(["lake", "env", "lean", str(lean_path)], cwd=ROOT,
                             capture_output=True, text=True)
    require((checked.returncode == 0) == kernel_ok,
            f"{name}: unexpected Lean outcome:\n{checked.stdout}\n{checked.stderr}")
    return {"case": name, "parser": "accepted",
            "kernel": "accepted" if kernel_ok else "rejected"}


def wrong_column_factor(source):
    needle = "  columnFactors := 1"
    require(source.count(needle) == 1, "Column-factor mutation did not identify one field")
    return source.replace(needle, "  columnFactors := ![(1 / 2), 1, 1, 1, 1, 1, 1, 1]")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path, nargs="?",
                        default=ROOT / "environments" / "admcycles-smoke-osx-arm64.json")
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    results = []
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-certificate-test-") as temporary:
        directory = Path(temporary)
        results.append(run_case(directory, "valid", report, kernel_ok=True))
        alternative = [[1, 1], [0, 1], [0, 1], [1, 2], [0, 1], [0, 1], [-2, 3]]
        results.append(run_case(directory, "alternative_witness", updated_report(
            report, set_field("arithmetic", "row_combination_witness", alternative)),
            kernel_ok=True))
        results.append(run_case(directory, "equivalent_loop_branch_swap", updated_report(
            report, swap_loop_branches), kernel_ok=True))
        kernel_mutations = [
            ("wrong_witness", change_witness),
            ("wrong_row_coefficient", change_entry("arithmetic", "fz_rows_monomial", 0, 1, [-59, 1])),
            ("wrong_generator_references", swap_generator_references),
            ("wrong_graph_incidence", change_graph),
            ("wrong_conversion", change_entry("coordinates", "pushforward_to_monomial", 1, 0, [0, 1])),
            ("wrong_inverse_conversion", change_entry("coordinates", "monomial_to_pushforward", 1, 0, [0, 1])),
            ("wrong_source_row", change_entry("arithmetic", "fz_rows_pushforward", 0, 1, [-59, 1])),
            ("wrong_requested_expression", set_field("arithmetic", "target_monomial", [[0, 1]] * 8)),
            ("wrong_source_request", set_field("arithmetic", "target_pushforward", [[0, 1]] * 8)),
        ]
        for name, change in kernel_mutations:
            results.append(run_case(directory, name, updated_report(report, change)))
        results.append(run_case(directory, "wrong_column_factor", report,
                                source_change=wrong_column_factor))
        parser_mutations = [
            ("boolean_schema_version", lambda report: report.__setitem__("schema_version", True)),
            ("wrong_external_label", change_label),
            ("wrong_locus", set_field("coordinates", "locus", "compact_type")),
            ("wrong_environment", set_field("environment", "sage", "0.0")),
            ("missing_rows", set_field("arithmetic", "fz_rows_monomial", [])),
            ("zero_denominator", change_entry("arithmetic", "fz_rows_monomial", 0, 0, [1, 0])),
            ("negative_denominator", change_entry("arithmetic", "fz_rows_monomial", 0, 0, [1, -1])),
            ("noninteger_coefficient", change_entry("arithmetic", "fz_rows_monomial", 0, 0, [1.0, 1])),
            ("code_in_rational", change_entry("arithmetic", "fz_rows_monomial", 0, 0, ["by decide", 1])),
        ]
        for name, change in parser_mutations:
            results.append(run_case(directory, name, updated_report(report, change), parse_ok=False))
        duplicate = json.dumps(report).replace('"schema_version": 1',
                                               '"schema_version": 1, "schema_version": 1')
        require(duplicate != json.dumps(report), "Duplicate-key mutation was not applied")
        results.append(run_case(directory, "duplicate_json_key", report, parse_ok=False,
                                raw_text=duplicate))
    print(json.dumps({"status": "passed", "scope": "fixed unmarked genus-two exchange",
                      "report_sha256": hashlib.sha256(args.report.read_bytes()).hexdigest(),
                      "sage_required": False, "cases": results}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, KeyError, ValueError) as error:
        print(f"admcycles certificate tests FAILED: {error}", file=sys.stderr)
        raise SystemExit(1)
