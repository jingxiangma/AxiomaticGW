#!/usr/bin/env python3
"""Compare native leading entries and inspect additional exact canonical matrices.

The held report used the full BP/L24 equations and their complete normalizer.
New rows are finite exploration. Matrix rank does not certify completeness of
the relation family, missing noncanonical support, or a uniform recursion.
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
from export_genus_two_leading import EXTRA_CASES
from explore_surface_bp import EXPECTED_CASES as BP_CASES
from explore_surface_l24 import EXPECTED_CASES as L24_CASES
from explore_genus_two_leading import required_columns

ROOT = Path(__file__).resolve().parents[1]
PRIOR = ROOT / "environments/genus-two-leading-exploration.json"
PRIOR_SHA256 = "9289dba27c5670a28d77dc65a325dfbc3f480b432fdfcdcb5be9ec904ddccd2e"


def column(q):
    require(q["genus"] == 2, "Wrong column genus")
    return ("descendant", q["genus"], tuple(q["curve"]),
            tuple(sorted(map(tuple, q["insertions"]))))


def held_column(q):
    return q[0], q[1], tuple(q[2]), tuple(map(tuple, q[3]))


def rational(c):
    require(type(c) is list and len(c) == 2 and all(type(x) is int for x in c)
            and c[1] > 0, "Invalid exact coefficient")
    result = Fraction(*c)
    require([result.numerator, result.denominator] == c, "Noncanonical rational")
    return result


def explore(payload):
    from sage.all import QQ, matrix
    from sage.version import version
    require(version == "10.9", "Review Sage version")
    require(hashlib.sha256(PRIOR.read_bytes()).hexdigest() == PRIOR_SHA256, "Held report changed")
    previous = json.loads(PRIOR.read_bytes(), object_pairs_hook=unique_object)
    held = {(e["family"], e["name"]): e for e in previous["equations"]}
    data = json.loads(payload, object_pairs_hook=unique_object)
    require(type(data["schema_version"]) is int and data["schema_version"] == 1, "Schema version")
    expected = {("BP", name): v for name, v in BP_CASES.items()}
    expected.update({("L24", name): v for name, v in L24_CASES.items()})
    expected.update({("BP", name): v for name, v in EXTRA_CASES.items()})
    keys = [(c["family"], c["name"]) for c in data["cases"]]
    require(len(keys) == len(set(keys)) and set(keys) == set(expected), "Request coverage")
    groups, rows = defaultdict(list), []
    for c in data["cases"]:
        key = c["family"], c["name"]
        r, beta, n, labels = expected[key]
        require((c["blowups"], tuple(c["curve"]), c["additional_markings"],
                 tuple(c["labels"])) == (r, beta, n, labels), "Request metadata changed")
        columns = [column(q) for q in c["columns"]]
        required = required_columns(r, beta)
        require(len(columns) == len(required) and set(columns) == set(required), "Missing column")
        values = list(map(rational, c["coefficients"]))
        require(len(values) == len(columns), "Coefficient count")
        entries = dict(zip(columns, values))
        if key in held:
            old = {}
            for term in held[key]["leading_terms"]:
                require(len(term["monomial"]) == 1, "Held support is not linear")
                q = held_column(term["monomial"][0])
                require(q in entries, "Uncompared held variable")
                old[q] = rational(term["coefficient"])
            require(entries == {q: old.get(q, Fraction(0)) for q in columns},
                    "Native entry disagrees with complete normalized equation: " + key[1])
        ordered = [entries[q] for q in required]
        groups[r, beta].append((key, ordered))
        rows.append({"family": key[0], "name": key[1],
                     "matches_held_full_normalization": True if key in held else None,
                     "columns": required,
                     "coefficients": [[x.numerator, x.denominator] for x in ordered]})
    systems = []
    for (r, beta), values in sorted(groups.items()):
        columns = required_columns(r, beta)
        m = matrix(QQ, [[QQ(x.numerator) / x.denominator for x in row] for _, row in values])
        pivots = list(map(int, m.pivots()))
        systems.append({"blowups": r, "curve": beta, "columns": columns,
                        "rows": [list(k) for k, _ in values],
                        "canonical_rank": int(m.rank()), "column_count": len(columns),
                        "pivot_columns": pivots,
                        "zero_columns": [i for i in range(len(columns)) if not any(m.column(i))]})
    paths = [Path(__file__).resolve(), ROOT / "scripts/export_genus_two_leading.py",
             ROOT / "scripts/GenusTwoLeading.lean",
             ROOT / "AxiomaticGW/Coefficients/AffineCoefficient.lean",
             ROOT / "AxiomaticGW/Surfaces/GenusTwoLeading.lean",
             ROOT / "AxiomaticGW/Surfaces/GenusTwoLeadingTerms.lean",
             ROOT / "AxiomaticGW/Surfaces/GenusTwoLeadingRelations.lean"]
    return {"schema_version": 1, "sage": version,
            "input_sha256": hashlib.sha256(payload).hexdigest(),
            "prior_report_sha256": PRIOR_SHA256,
            "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in paths},
            "scope": "Nineteen comparisons to held full equations; six new canonical rows. Finite ranks only, with no assertion of full support, uniform pivots or finite-seed sufficiency.",
            "comparison_scope": "Both evaluators share relation data and direct normalization. The held full equations had separate incidence-based admcycles checks. This run adds no independent CohFT or localization verification.",
            "equations": rows, "systems": systems}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="genus-two-leading-matrix-") as cache:
        for variable, name in (("DOT_SAGE", "sage"), ("MPLCONFIGDIR", "matplotlib"),
                               ("XDG_CACHE_HOME", "xdg")):
            path = Path(cache) / name
            path.mkdir()
            os.environ[variable] = str(path)
        report = explore(args.input.read_bytes())
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"equations": len(report["equations"]), "systems": [
        {k: s[k] for k in ("blowups", "curve", "canonical_rank", "column_count", "zero_columns")}
        for s in report["systems"]]}))


if __name__ == "__main__":
    main()
