#!/usr/bin/env python3
"""Verify the archived native R2 corpus, source pins, coverage, and small fixtures.

This checks supplemental runtime evidence. Kernel completeness and the small
numeral proofs live in GraphEnumeration and its Lean regression module.
"""

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path,
                        default=ROOT / "environments" / "graph-corpus-native-osx-arm64.json")
    parser.add_argument("--verify-executable", action="store_true",
                        help="Also require the current native binary to match the recorded hash")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    require(manifest["status"] == "passed_native_runtime" and
            manifest["child_exit_code"] == 0, "Native execution was not successful")
    output = ROOT / manifest["archived_output"]
    diagnostics = ROOT / manifest["archived_diagnostics"]
    require(digest(output) == manifest["output_sha256"], "Corpus hash mismatch")
    require(digest(diagnostics) == manifest["diagnostics_sha256"], "Diagnostics hash mismatch")
    for name, pin in manifest["source_sha256"].items():
        require(digest(ROOT / name) == pin, f"Source changed: {name}")
    if args.verify_executable:
        require(digest(ROOT / ".lake/build/bin/graphCorpus") == manifest["binary_sha256"],
                "Executable hash mismatch")
    expected = {(g, n, d) for g in range(3) for n in range(7) for d in range(4)
                if 3 <= 2 * g + n}
    rows = [json.loads(line) for line in output.read_text().splitlines()]
    observed = {}
    for row in rows:
        require(set(row) == {"genus", "markings", "bound", "count", "elapsed_ms"},
                "Wrong corpus row fields")
        require(all(type(value) is int and value >= 0 for value in row.values()),
                "Invalid corpus value")
        case = row["genus"], row["markings"], row["bound"]
        require(case in expected and case not in observed, "Unexpected or duplicate case")
        observed[case] = row["count"]
    require(set(observed) == expected and len(rows) == 68, "Incomplete coverage")
    require(manifest["case_count"] == manifest["expected_case_count"] == len(rows),
            "Incorrect manifest coverage")
    require(all(observed[g, n, d] <= observed[g, n, d + 1]
                for g, n, d in expected if d < 3), "Nonmonotone bounded counts")
    fixtures = {(0, 3, 0): 1, (0, 3, 1): 5, (0, 4, 0): 1, (0, 4, 1): 9,
                (1, 1, 1): 4, (2, 0, 2): 12}
    require(all(observed[case] == count for case, count in fixtures.items()),
            "Disagreement with a kernel-checked GraphEnumeration fixture")
    print(json.dumps({"cases": len(rows), "source_pins": len(manifest["source_sha256"]),
                      "kernel_fixture_comparisons": len(fixtures),
                      "largest_case": observed[2, 6, 3],
                      "binary_checked": args.verify_executable,
                      "scope": "Supplemental native evidence; no geometric quotient claim"},
                     sort_keys=True))


if __name__ == "__main__":
    main()
