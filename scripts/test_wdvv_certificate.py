#!/usr/bin/env python3
"""Offline marked WDVV replay and corruption regressions, using no Sage.

Every case holds the compiled graph frame, raw factors, rows, and requested
consequence fixed. Parser rejection is distinguished from Lean rejection.
Equivalent vertex and branch presentations remain acceptable.
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
EXPORTER = ROOT / "scripts" / "export_wdvv_certificate.py"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run_case(directory, name, report, parser_ok=True, kernel_ok=False, raw_text=None):
    print(f"Checking {name}", file=sys.stderr, flush=True)
    incoming = directory / f"{name}.json"
    incoming.write_text(json.dumps(report) if raw_text is None else raw_text)
    exported = subprocess.run([sys.executable, str(EXPORTER), str(incoming)], cwd=ROOT,
                              capture_output=True, text=True)
    require((exported.returncode == 0) == parser_ok,
            f"{name}: unexpected parser result: {exported.stderr}")
    if not parser_ok:
        require(not exported.stdout, f"{name}: parser emitted partial replay")
        return {"case": name, "parser": "rejected"}
    path = directory / f"{name}.lean"
    path.write_text(exported.stdout)
    checked = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                             capture_output=True, text=True)
    require((checked.returncode == 0) == kernel_ok,
            f"{name}: unexpected kernel result:\n{checked.stdout}\n{checked.stderr}")
    if kernel_ok:
        require(not checked.stdout and not checked.stderr, f"{name}: replay emitted diagnostics")
    return {"case": name, "parser": "accepted",
            "kernel": "accepted" if kernel_ok else "rejected"}


def changed(report, mutation):
    result = copy.deepcopy(report)
    mutation(result)
    return result


def branch_swap(report):
    report["graphs"][0]["endpoints"][0].reverse()


def vertex_swap(report):
    graph = report["graphs"][1]
    graph["leg_vertices"] = [1 - v for v in graph["leg_vertices"]]
    graph["endpoints"] = [[1 - v for v in pair] for pair in graph["endpoints"]]


def wrong_partition(report):
    report["graphs"][0]["leg_vertices"] = [0, 1, 0, 1]


def kappa_column(report):
    report["graphs"][0] = {
        "index": 0, "genus": [0], "leg_vertices": [0] * 4,
        "endpoints": [], "kappa": [[1]], "leg_psi": [0] * 4, "half_psi": [],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path, nargs="?",
                        default=ROOT / "environments" / "wdvv-candidate-osx-arm64.json")
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    results = []
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-wdvv-replay-") as temporary:
        directory = Path(temporary)
        for name, mutation in (("valid", lambda r: None),
                               ("equivalent_vertex_swap", vertex_swap),
                               ("equivalent_branch_swap", branch_swap)):
            results.append(run_case(directory, name, changed(report, mutation), kernel_ok=True))
        kernel_mutations = [
            ("changed_external_partition", wrong_partition),
            ("different_valid_kappa_column", kappa_column),
            ("wrong_raw_factor", lambda r: r["column_factors"].__setitem__(0, [1, 2])),
            ("changed_row_coefficient", lambda r: r["rows"][0].__setitem__(2, [1, 1])),
            ("swapped_generator_rows", lambda r: r["rows"].reverse()),
            ("changed_claim", lambda r: r.__setitem__("requested", [[0, 1]] * 3)),
            ("wrong_witness", lambda r: r["witness"].__setitem__(1, [2, 1])),
            ("wrong_vertex_genus", lambda r: r["graphs"][0]["genus"].__setitem__(0, 1)),
            ("disconnected_loop", lambda r: r["graphs"][0]["endpoints"].__setitem__(0, [0, 0])),
            ("extra_leg_psi", lambda r: r["graphs"][0]["leg_psi"].__setitem__(0, 1)),
        ]
        for name, mutation in kernel_mutations:
            results.append(run_case(directory, name, changed(report, mutation)))
        parser_mutations = [
            ("wrong_locus", lambda r: r.__setitem__("locus", "compact_type")),
            ("wrong_label_domain", lambda r: r.__setitem__("markings", [0, 1, 2, 4])),
            ("wrong_genus_frame", lambda r: r.__setitem__("genus", 1)),
            ("wrong_label_conversion", lambda r: r["source_label_map"][0].__setitem__(1, 3)),
            ("wrong_normalization", lambda r: r.__setitem__("normalization", "divide_by_aut")),
            ("wrong_generator_reference", lambda r: r["relation_ids"].reverse()),
            ("floating_coefficient", lambda r: r["witness"].__setitem__(0, [1.0, 1])),
            ("boolean_coefficient", lambda r: r["witness"].__setitem__(0, [True, 1])),
            ("boolean_label_conversion", lambda r: r["source_label_map"][0].__setitem__(1, False)),
            ("floating_label_conversion", lambda r: r["source_label_map"][0].__setitem__(1, 0.0)),
            ("zero_denominator", lambda r: r["witness"].__setitem__(0, [1, 0])),
            ("missing_graph_field", lambda r: r["graphs"][0].pop("leg_psi")),
            ("unknown_graph_field", lambda r: r["graphs"][0].__setitem__("hidden_factor", 2)),
            ("out_of_range_edge", lambda r: r["graphs"][0]["endpoints"].__setitem__(0, [0, 2])),
            ("reordered_graph_slots", lambda r: r["graphs"][0].__setitem__("index", 1)),
            ("changed_tool_pin", lambda r: r["environment"].__setitem__("admcycles", "1.5")),
        ]
        for name, mutation in parser_mutations:
            results.append(run_case(directory, name, changed(report, mutation), parser_ok=False))
        duplicate = json.dumps(report).replace('"schema_version": 1',
                                               '"schema_version": 1, "schema_version": 1')
        results.append(run_case(directory, "duplicate_json_key", report,
                                parser_ok=False, raw_text=duplicate))
    print(json.dumps({
        "status": "passed", "case_count": len(results), "cases": results,
        "report_sha256": hashlib.sha256(args.report.read_bytes()).hexdigest(),
        "scope": "Fixed marked WDVV candidate exchange and offline Lean replay; "
                 "geometric boundary equality and surface GW applicability remain inputs.",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
