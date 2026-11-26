#!/usr/bin/env python3
"""Independently normalize BP equations using recursive GW equations.

The input BP graph expansion is rechecked with Sage/admcycles. Tail matrices
come from the pinned native GKM comparison, not this new Lean normalizer.
Lower-genus values in the original BP expansion remain shared Lean values.
This checks finite equations; it does not assert a full genus-two recurrence.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
from itertools import product
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
from explore_surface_bp import EXPECTED_CASES, ROOT, collect, codim, energy, explore, query_key
from export_admcycles_certificate import require

CALIBRATION = ROOT / "environments/gkm-first-calibration-comparison.json"
CALIBRATION_SHA = "e50d50dc43b8be23e15a33234503157cdc2fd293774555dc0339d0d7ee52474c"
EXPECTED_PROBES = {
    "f1_2E_psiE_ptpt": (1, (2, (2, 0), ((2, 0), (2, 0), (3, 1)))),
    "f1_2E_psiE_Eptpt": (1, (2, (2, 0), ((2, 0), (2, 0), (3, 0), (3, 1)))),
    "f1_EF_psiE_ptptpt": (1, (2, (1, 1), ((2, 0), (2, 0), (2, 0), (3, 1)))),
    "bl2_2E1_psiE1_ptpt": (2, (2, (2, 0, 0), ((2, 0), (2, 0), (3, 1)))),
    "p2_line_psi3pt_retained": (0, (2, (1,), ((2, 3),))),
}


def clean(p):
    return {m: c for m, c in p.items() if c}


def add_scaled(out, p, c):
    for m, value in p.items():
        out[m] += c * value


def tagged_collect(terms):
    out = defaultdict(Fraction)
    for t in terms:
        m = tuple(sorted((v["kind"], *query_key(v["query"])) for v in t["monomial"]))
        require(all(v[0] in ("ancestor", "descendant") for v in m), "Unknown variable interpretation")
        out[m] += Fraction(*t["coefficient"])
    return clean(out)


def serial(p):
    return [{"monomial": m, "coefficient": [c.numerator, c.denominator]}
            for m, c in sorted(p.items())]


def matrices():
    require(hashlib.sha256(CALIBRATION.read_bytes()).hexdigest() == CALIBRATION_SHA,
            "Review native GKM calibration pin")
    answer = {}
    for case in json.loads(CALIBRATION.read_bytes())["cases"]:
        r = int(case["target"][1:])
        codes = [0 if b == "unit" else 1 if b == "H" else 2 if b == "pt" else 2 + int(b[1:])
                 for b in case["basis"]]
        require(case["matches"] and case["inverse_loop_power"] == 1, "Unverified tail matrix")
        answer[r, tuple(case["class"])] = {(codes[i], codes[j]): Fraction(*value)
            for i, row in enumerate(case["operator_ordinary"]) for j, value in enumerate(row)}
    return answer


def divisor_factor(r, beta, label):
    if label == 0:
        return 0
    if label == 2:
        return 1
    # Effective coordinates: dL; aE+bF; aE1+bE2+cL12.
    intersections = (beta[0],) if r == 0 else (
        (beta[1], beta[1] - beta[0]) if r == 1 else
        (beta[2], beta[2] - beta[0], beta[2] - beta[1]))
    return intersections[0 if label == 1 else label - 2]


def atom(r, g, beta, insertions):
    if sum(codim(b) + p for b, p in insertions) != energy(r, beta) + g - 1 + len(insertions):
        return {}
    return {(("descendant", g, beta, tuple(sorted(insertions))),): Fraction(1)}


def primary(r, g, beta, labels):
    c = 1
    for d in labels:
        c *= divisor_factor(r, beta, d)
    return {m: c * v for m, v in atom(r, g, beta, ((2, 0),) * labels.count(2)).items() if c * v}


def descendant(r, g, beta, b, labels, positive_square=False, omit_cup=False):
    """Remove one primary at a time; independent of Lean's closed count/product formula."""
    labels = list(labels)
    if 0 in labels:
        labels.remove(0)
        return primary(r, g, beta, [b] + labels)
    if b == 0:
        return {m: (2 * g - 2 + len(labels)) * c for m, c in primary(r, g, beta, labels).items()}
    divisors = [d for d in labels if d != 2]
    if not divisors:
        return atom(r, g, beta, ((b, 1),) + ((2, 0),) * len(labels))
    d = divisors[0]
    labels.remove(d)
    result = defaultdict(Fraction)
    add_scaled(result, descendant(r, g, beta, b, labels, positive_square, omit_cup),
               divisor_factor(r, beta, d))
    cup = (1 if b == 1 or positive_square else -1) if b == d else 0
    if not omit_cup:
        add_scaled(result, primary(r, g, beta, [2] + labels), cup)
    return clean(result)


def ancestor(r, q, calibration, tail_sign=-1, **mutation):
    g, beta, ins = q
    require(g >= 2, "Unexpected unreconstructed low genus")
    degree = sum(p for _, p in ins)
    if degree == 0:
        return primary(r, g, beta, [b for b, _ in ins])
    if degree != 1:
        return {(("ancestor", g, beta, ins),): Fraction(1)}
    b = next(b for b, p in ins if p == 1)
    labels = [d for d, p in ins if p == 0]
    answer = defaultdict(Fraction, descendant(r, g, beta, b, labels, **mutation))
    for tail in product(*(range(x + 1) for x in beta)):
        if not any(tail):
            continue
        main = tuple(x - y for x, y in zip(beta, tail))
        require(energy(r, main) < energy(r, beta), "Tail does not strictly lower energy")
        require((r, tail) in calibration, "Uncovered GKM tail class")
        for row in range(r + 3):
            add_scaled(answer, primary(r, g, main, [row] + labels),
                       tail_sign * calibration[r, tail][row, b])
    return clean(answer)


def substitute(r, p, calibration, **mutation):
    answer = defaultdict(Fraction)
    for monomial, c in p.items():
        require(len(monomial) <= 1, "Non-affine input")
        add_scaled(answer, ancestor(r, monomial[0], calibration, **mutation) if monomial
                   else {(): Fraction(1)}, c)
    return clean(answer)


def check(ancestor_payload, normalized_payload):
    from sage.all import QQ, matrix
    original_report = explore(ancestor_payload)
    original = {c["name"]: c for c in json.loads(ancestor_payload)["cases"]}
    data = json.loads(normalized_payload)
    require(data["schema_version"] == 1, "Unknown normalized schema")
    names = [c["name"] for c in data["cases"]]
    require(len(names) == len(EXPECTED_CASES) and set(names) == set(EXPECTED_CASES), "Coverage changed")
    calibration = matrices()
    reports, polynomials, substitutions = [], {}, []
    for case in data["cases"]:
        name = case["name"]
        r, beta, n, labels = EXPECTED_CASES[name]
        require((case["blowups"], tuple(case["curve"]), case["additional_markings"],
                 tuple(case["labels"])) == (r, beta, n, labels), "Request changed")
        raw = collect(original[name]["genus_two_terms"])
        require(collect(case["ancestor_terms"]) == raw, "Ancestor expansion changed")
        required = {query_key(q) for t in case["ancestor_terms"] for q in t["monomial"]}
        supplied = [query_key(s["ancestor"]) for s in case["substitutions"]]
        require(len(supplied) == len(set(supplied)) and set(supplied) == required,
                "Missing or repeated ancestor substitution")
        for s in case["substitutions"]:
            q = query_key(s["ancestor"])
            expected = ancestor(r, q, calibration)
            require(tagged_collect(s["terms"]) == expected, f"Individual substitution: {name}, {q}")
            substitutions.append((r, q, expected))
        expected = substitute(r, raw, calibration)
        require(tagged_collect(case["normalized_terms"]) == expected, f"Normalized equation: {name}")
        require(all(len(m) <= 1 for m in expected), "Nonlinear output")
        unknowns = [m[0] for m in expected if m]
        require(all(q[0] == "descendant" and q[1] == 2 for q in unknowns), "Unexpected residual sector")
        require(all(all(x <= b for x, b in zip(q[2], beta)) for q in unknowns), "Full class grew")
        polynomials[name] = expected
        reports.append({"name": name, "source_ancestor_monomials": len(raw),
                        "normalized_monomials": len(expected), "individual_substitutions": len(supplied),
                        "same_class_unknowns": sum(q[2] == beta for q in unknowns),
                        "smaller_class_unknowns": sum(q[2] != beta for q in unknowns),
                        "equation": serial(expected), "equal": True})
    probe_names = [p["name"] for p in data["probes"]]
    require(len(probe_names) == len(EXPECTED_PROBES) and set(probe_names) == set(EXPECTED_PROBES),
            "Probe coverage changed")
    probe_report = []
    for probe in data["probes"]:
        r, q = EXPECTED_PROBES[probe["name"]]
        require((probe["blowups"], query_key(probe["ancestor"])) == (r, q), "Probe request changed")
        expected = ancestor(r, q, calibration)
        require(tagged_collect(probe["terms"]) == expected, "Normalization probe disagrees")
        substitutions.append((r, q, expected))
        probe_report.append({"name": probe["name"], "equal": True, "equation": serial(expected)})
    mutations = []
    for label, mutation in [("positive_rational_tail_sign", {"tail_sign": 1}),
                            ("missing_divisor_cup_term", {"omit_cup": True}),
                            ("positive_exceptional_square", {"positive_square": True})]:
        witnesses = sum(ancestor(r, q, calibration, **mutation) != expected
                        for r, q, expected in substitutions)
        require(witnesses > 0, f"Mutation lacked a distinguishing case: {label}")
        mutations.append({"name": label, "distinguishing_substitutions": witnesses})
    ranks = []
    for r, beta in sorted({(v[0], v[1]) for v in EXPECTED_CASES.values()}):
        family = [polynomials[name] for name, v in EXPECTED_CASES.items() if v[:2] == (r, beta)]
        columns = sorted({m[0] for p in family for m in p if m and m[0][2] == beta})
        rows = [[QQ(p.get((q,), 0)) for q in columns] for p in family]
        ranks.append({"blowups": r, "curve": beta, "equations": len(rows),
                      "same_class_unknowns": len(columns),
                      "rank": int(matrix(QQ, len(rows), len(columns), sum(rows, [])).rank())})
    return {"schema_version": 1, "scope": "Finite normalized BP equations; no uniqueness claim",
            "sage": original_report["sage"], "admcycles": original_report["admcycles"],
            "online_lookup": False, "cases": reports, "probes": probe_report,
            "sample_matrix_ranks": ranks,
            "mutations_rejected": mutations,
            "original_graph_mutations_rejected": original_report["mutations_rejected"],
            "ancestor_payload_sha256": hashlib.sha256(ancestor_payload).hexdigest(),
            "normalized_payload_sha256": hashlib.sha256(normalized_payload).hexdigest(),
            "calibration_gkm_sha256": CALIBRATION_SHA,
            "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in [Path(__file__).resolve(), ROOT / "scripts/SurfaceBPNormalized.lean",
                          ROOT / "scripts/explore_surface_bp.py"]},
            "admcycles_module_sha256": original_report["admcycles_module_sha256"],
            "independence": "Graph contraction is recomputed with admcycles; normalization uses recursive string/divisor/dilaton and pinned native GKM matrices. Original lower-genus BP values are shared Lean outputs. No independent genus-two values are asserted."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ancestor-input", type=Path)
    parser.add_argument("--lean-input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    def payload(path, target):
        if path:
            return path.read_bytes()
        subprocess.run(["lake", "build", target], cwd=ROOT, check=True, stdout=sys.stderr)
        return subprocess.check_output([str(ROOT / ".lake/build/bin" / target)], cwd=ROOT)
    original = payload(args.ancestor_input, "surfaceBP")
    normalized = payload(args.lean_input, "surfaceBPNormalized")
    with tempfile.TemporaryDirectory(prefix="normalized-bp-sage-") as cache:
        for variable, name in (("DOT_SAGE", "sage"), ("ADMCYCLES_CACHE_DIR", "admcycles"),
                               ("MPLCONFIGDIR", "matplotlib"), ("XDG_CACHE_HOME", "xdg")):
            location = Path(cache) / name
            location.mkdir()
            os.environ[variable] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        report = check(original, normalized)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"cases": len(report["cases"]), "mutations": report["mutations_rejected"],
                      "output": str(args.output)}))


if __name__ == "__main__":
    main()
