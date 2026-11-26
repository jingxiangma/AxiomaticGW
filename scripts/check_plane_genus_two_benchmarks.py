#!/usr/bin/env python3
"""Compare all twelve plane candidates with the held BP table, without certifying them."""

import argparse
import json
from pathlib import Path

from export_plane_genus_two_scalar import rational, read_report, requests, require

MANIFEST = Path(__file__).resolve().parents[1] / "environments/plane-genus-two-benchmarks.json"


def check(raw):
    report, _ = read_report(raw, 4)
    held = json.loads(MANIFEST.read_text())
    require(held["degree_bound"] == 4 and held["energy_bound"] == 12,
            "Changed fixed benchmark bound")
    require(len(held["queries"]) == 12, "Incomplete held query coverage")
    for d, row in enumerate(report["rows"], 1):
        for i, family in enumerate(["N", "H", "P"]):
            expected = held["queries"][3 * (d - 1) + i]
            query = {k: expected[k] for k in ["genus", "curve", "insertions"]}
            require(expected["target"] == "P2" and expected["family"] == family
                    and json.dumps(query, sort_keys=True) ==
                    json.dumps(requests(d)[i], sort_keys=True), "Changed held full query")
            rational(expected["expected"])
            require(row["values"][i] == expected["expected"],
                    f"Published value mismatch for {family}_{d}")
    return 12


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    args = parser.parse_args()
    count = check(args.report.read_bytes())
    print(f"All {count} full requests match the published table; kernel replay is separate.")


if __name__ == "__main__":
    main()
