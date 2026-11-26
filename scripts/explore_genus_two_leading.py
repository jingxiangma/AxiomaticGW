#!/usr/bin/env python3
"""Inspect the combined BP/L24 leading matrices without claiming uniform rank.

This reuses the previously checked native equation payloads and the existing
recursive reference normalizer. All canonical primary/first-descendant columns
are included, even if absent from the sampled equations. Calibration is used
only to compare extraction with the complete normalized equation.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
from export_admcycles_certificate import require, unique_object
from explore_surface_bp import EXPECTED_CASES as BP_CASES, collect, energy
from explore_surface_l24 import EXPECTED_CASES as L24_CASES
from explore_normalized_surface_bp import (
    add_scaled, clean, descendant, matrices, primary, serial, substitute,
)

ROOT = Path(__file__).resolve().parents[1]
INPUT_SHA256 = {
    "BP": "dddb622b1b3b8b2a5c15c8cf393b429dfd7d5d348b1b8a2198f9b87675cf44e3",
    "L24": "2fb86e1c36ce730da3d0bb70a94461f0a935aebe2cb08a076b6aa29108dc905d",
}


def direct(r, query):
    g, beta, ins = query
    degree = sum(p for _, p in ins)
    if degree == 0:
        return primary(r, g, beta, [b for b, _ in ins])
    if degree == 1:
        b = next(b for b, p in ins if p == 1)
        return descendant(r, g, beta, b, [d for d, p in ins if p == 0])
    return {(("ancestor", g, beta, ins),): Fraction(1)}


def required_columns(r, beta):
    e = energy(r, beta)
    columns = [("descendant", 2, beta, ((2, 0),) * (e + 1))]
    for b in [1] + list(range(3, r + 3)):
        columns.append(("descendant", 2, beta, tuple(sorted(((b, 1),) + ((2, 0),) * e))))
    if e > 0:
        columns.append(("descendant", 2, beta, tuple(sorted(((2, 1),) + ((2, 0),) * (e - 1)))))
    return sorted(columns)


def explore(payloads):
    from sage.all import QQ, matrix
    from sage.version import version
    require(version == "10.9", "Review the Sage version")
    calibration = matrices()
    groups, checks = defaultdict(list), []
    for family, payload in payloads.items():
        require(hashlib.sha256(payload).hexdigest() == INPUT_SHA256[family],
                "Previously verified equation payload changed: " + family)
        data = json.loads(payload, object_pairs_hook=unique_object)
        require(type(data["schema_version"]) is int and data["schema_version"] == 1,
                "Unexpected payload version")
        expected = BP_CASES if family == "BP" else L24_CASES
        names = [c["name"] for c in data["cases"]]
        require(len(names) == len(expected) and set(names) == set(expected), "Case coverage changed")
        for case in data["cases"]:
            r, beta, n, labels = expected[case["name"]]
            require((case["blowups"], tuple(case["curve"]), case["additional_markings"],
                     tuple(case["labels"])) == (r, beta, n, labels), "Request changed")
            p = collect(case["genus_two_terms"])
            require(all(len(m) <= 1 for m in p), "Non-affine input")
            leading = defaultdict(Fraction)
            for m, c in p.items():
                if m and m[0][1] == beta:
                    add_scaled(leading, direct(r, m[0]), c)
            leading = clean(leading)
            full = substitute(r, p, calibration)
            projected = {m: c for m, c in full.items() if m and m[0][2] == beta}
            require(leading == projected, "Leading extraction changed a coefficient")
            require(all(len(m) == 1 and m[0][1] == 2 for m in leading), "Wrong leading support")
            groups[r, beta].append((family, case["name"], leading))
            checks.append({"family": family, "name": case["name"],
                           "equal_to_full_normalized_projection": True,
                           "leading_terms": serial(leading)})
    systems = []
    for (r, beta), rows in sorted(groups.items()):
        required = required_columns(r, beta)
        extra = sorted({m[0] for _, _, p in rows for m in p} - set(required))
        columns = required + extra
        entries = [[QQ(p.get((q,), 0)) for q in columns] for _, _, p in rows]
        full_matrix = matrix(QQ, len(rows), len(columns), sum(entries, []))
        ranks = {}
        for family in ("BP", "L24"):
            selected = [row for row, meta in zip(entries, rows) if meta[0] == family]
            ranks[family] = int(matrix(QQ, len(selected), len(columns), sum(selected, [])).rank())
        systems.append({
            "blowups": r, "curve": beta,
            "rows": [{"family": f, "name": name} for f, name, _ in rows],
            "required_columns": required, "additional_columns": extra,
            "matrix": [[[int(c.numerator()), int(c.denominator())] for c in row] for row in entries],
            "family_ranks": ranks, "combined_rank": int(full_matrix.rank()),
            "column_count": len(columns),
            "missing_rank": len(columns) - int(full_matrix.rank()),
        })
    sources = [Path(__file__).resolve(), ROOT / "scripts/explore_normalized_surface_bp.py",
               ROOT / "scripts/explore_surface_bp.py", ROOT / "scripts/explore_surface_l24.py",
               ROOT / "environments/gkm-first-calibration-comparison.json",
               ROOT / "AxiomaticGW/Surfaces/OnePsiSupport.lean",
               ROOT / "AxiomaticGW/Surfaces/GenusTwoNormalizedSupport.lean"]
    return {"schema_version": 1, "sage": version, "input_sha256": INPUT_SHA256,
            "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in sources},
            "scope": "Finite sampled leading matrices, including absent canonical columns; no uniform pivot or finite-seed sufficiency claim.",
            "comparison_scope": "Reuses the existing recursive reference normalizer and pinned GKM calibration. Original graph comparisons and numerical low-genus values are shared; they are not independently rechecked here.",
            "equations": checks, "systems": systems}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bp-input", type=Path, required=True)
    parser.add_argument("--l24-input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="genus-two-leading-") as cache:
        for variable, name in (("DOT_SAGE", "sage"), ("MPLCONFIGDIR", "matplotlib"),
                               ("XDG_CACHE_HOME", "xdg")):
            path = Path(cache) / name
            path.mkdir()
            os.environ[variable] = str(path)
        report = explore({"BP": args.bp_input.read_bytes(), "L24": args.l24_input.read_bytes()})
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"equations": len(report["equations"]), "systems": [
        {k: s[k] for k in ("blowups", "curve", "combined_rank", "column_count", "missing_rank")}
        for s in report["systems"]]}))


if __name__ == "__main__":
    main()
