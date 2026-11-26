#!/usr/bin/env python3
"""Offline Getzler replay and corruption regressions using ordinary Python/Lean.

All incoming graphs and tables are checked against the independently compiled
33-column frame. Parser failures and kernel failures are reported separately.
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
EXPORTER = ROOT / "scripts" / "export_getzler_certificate.py"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def changed(report, mutation):
    result = copy.deepcopy(report)
    mutation(result)
    return result


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


def vertex_permutation(report):
    graph = report["graphs"][3]
    permutation = [2, 0, 1]
    graph["genus"] = [1, 0, 0]
    graph["genus"] = [graph["genus"][permutation.index(i)] for i in range(3)]
    graph["leg_vertices"] = [permutation[v] for v in graph["leg_vertices"]]
    graph["endpoints"] = [[permutation[v] for v in pair] for pair in graph["endpoints"]]


def edge_and_branch_permutation(report):
    graph = report["graphs"][25]
    graph["endpoints"] = [list(reversed(pair)) for pair in reversed(graph["endpoints"])]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path, nargs="?",
                        default=ROOT / "environments" / "getzler-candidate-osx-arm64.json")
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    results = []
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-getzler-replay-") as temporary:
        directory = Path(temporary)
        good = [("valid", lambda r: None), ("equivalent_vertex_permutation", vertex_permutation),
                ("equivalent_edge_branch_permutation", edge_and_branch_permutation),
                ("equivalent_rational_witness", lambda r: r.update(witness=[[-2, 8]]))]
        for name, mutation in good:
            results.append(run_case(directory, name, changed(report, mutation), kernel_ok=True))
        bad = [
            ("different_valid_marking_partition",
             lambda r: r["graphs"][0].update(leg_vertices=[1, 2, 1, 2])),
            ("loop_replaces_parallel_edges",
             lambda r: r["graphs"][30].update(endpoints=[[0, 0], [0, 1]])),
            ("disconnected_graph",
             lambda r: r["graphs"][0].update(endpoints=[[0, 0], [1, 2]])),
            ("wrong_vertex_genus", lambda r: r["graphs"][0].update(genus=[0, 0, 0])),
            ("added_kappa", lambda r: r["graphs"][0]["kappa"][0].__setitem__(0, 1)),
            ("added_external_psi", lambda r: r["graphs"][3]["leg_psi"].__setitem__(3, 1)),
            ("added_node_psi", lambda r: r["graphs"][25]["half_psi"][0].__setitem__(1, 1)),
            ("raw_column_factor", lambda r: r["column_factors"].__setitem__(25, [1, 2])),
            ("elliptic_stabilizer_double_counted",
             lambda r: r["orbifold_factors"].__setitem__(15, [1, 2])),
            ("loop_factor_omitted", lambda r: r["orbifold_factors"].__setitem__(29, [1, 1])),
            ("wrong_named_cycle", lambda r: r["stratum_ids"].__setitem__(3, "delta24")),
            ("changed_original_row", lambda r: r["rows"][0].__setitem__(3, [-2, 1])),
            ("changed_requested_claim", lambda r: r["requested"].__setitem__(25, [-1, 4])),
            ("zero_witness", lambda r: r.update(witness=[[0, 1]])),
        ]
        for name, mutation in bad:
            results.append(run_case(directory, name, changed(report, mutation)))
        malformed = [
            ("wrong_locus", lambda r: r.update(locus="compact_type")),
            ("wrong_frame", lambda r: r.update(frame="getzler_mbar_1_4_v2")),
            ("wrong_labels", lambda r: r.update(markings=[1, 2, 3, 4])),
            ("wrong_source_labels", lambda r: r["source_label_map"][0].__setitem__(1, 1)),
            ("boolean_source_label", lambda r: r["source_label_map"][0].__setitem__(1, False)),
            ("wrong_reference", lambda r: r.update(relation_ids=["getzler_1_1"])),
            ("wrong_normalization", lambda r: r.update(normalization="orbifold_cycle")),
            ("float_coefficient", lambda r: r["rows"][0].__setitem__(0, [12.0, 1])),
            ("boolean_coefficient", lambda r: r["rows"][0].__setitem__(0, [True, 1])),
            ("zero_denominator", lambda r: r["witness"].__setitem__(0, [-1, 0])),
            ("boolean_incidence", lambda r: r["graphs"][0]["leg_vertices"].__setitem__(0, True)),
            ("vertex_out_of_range", lambda r: r["graphs"][0]["endpoints"][0].__setitem__(0, 3)),
            ("reordered_graph_slots", lambda r: r["graphs"].reverse()),
            ("missing_graph_field", lambda r: r["graphs"][0].pop("leg_psi")),
            ("unknown_graph_field", lambda r: r["graphs"][0].update(trusted=True)),
            ("unknown_report_field", lambda r: r.update(trusted=True)),
            ("wrong_tool_pin", lambda r: r["environment"].update(admcycles="1.5")),
        ]
        for name, mutation in malformed:
            results.append(run_case(directory, name, changed(report, mutation), parser_ok=False))
        duplicate = json.dumps(report).replace('"schema_version": 1',
                    '"schema_version": 1, "schema_version": 1', 1)
        results.append(run_case(directory, "duplicate_json_key", report,
                                parser_ok=False, raw_text=duplicate))
    manifest = {"schema_version": 1, "frame": "getzler_mbar_1_4_v1",
                "report_sha256": hashlib.sha256(args.report.read_bytes()).hexdigest(),
                "offline": True, "sage_used": False, "cases": results,
                "scope": "Fixed 33-column Getzler exchange; "
                         "geometric validity is a separate input."}
    (ROOT / "environments" / "getzler-certificate-regressions.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(f"{len(results)} Getzler exchange cases passed")


if __name__ == "__main__":
    main()
