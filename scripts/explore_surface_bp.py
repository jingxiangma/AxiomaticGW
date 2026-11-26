#!/usr/bin/env python3
"""Compare surface BP polynomials with independent admcycles graph contractions.

The raw comparison uses only full classes, the surface metric and dimension.
The partially reconstructed comparison then substitutes the exported, already
formalized lower-genus algorithms. It does not certify those numerical values
independently, prove a genus-two pivot, or identify ancestors with descendants.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
import hashlib
import importlib.metadata
from itertools import product
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
from export_admcycles_certificate import require
from search_belorousski_pandharipande import relabel

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "environments/belorousski-pandharipande.json"
SOURCE_SHA256 = "5868b2f3ef1e5a45e6175b6349566b72c778f4ab028ef941b43498fd0ee8d1bc"
EXPECTED_CASES = {
    "p2_zero_HH1": (0, (0,), 0, (1, 1, 0)),
    "p2_line_HHH": (0, (1,), 2, (1, 1, 1)),
    "f1_E_EEE": (1, (1, 0), 0, (3, 3, 3)),
    "f1_F_HHH": (1, (0, 1), 1, (1, 1, 1)),
    "f1_F_EHH": (1, (0, 1), 1, (3, 1, 1)),
    "bl2_E1_E1E1E1": (2, (1, 0, 0), 0, (3, 3, 3)),
    "bl2_E2_E1E1E1": (2, (0, 1, 0), 0, (3, 3, 3)),
    "bl2_E2_E2E2E2": (2, (0, 1, 0), 0, (4, 4, 4)),
    "bl2_L_HHH": (2, (0, 0, 1), 0, (1, 1, 1)),
    "bl2_L_E1E2H": (2, (0, 0, 1), 0, (3, 4, 1)),
}


def query_key(q):
    return q["genus"], tuple(q["curve"]), tuple(sorted(map(tuple, q["insertions"])))


def collect(terms):
    answer = defaultdict(Fraction)
    for term in terms:
        answer[tuple(sorted(query_key(q) for q in term["monomial"]))] += Fraction(*term["coefficient"])
    return {m: c for m, c in answer.items() if c}


def digest(terms):
    serial = [[m, [c.numerator, c.denominator]] for m, c in sorted(terms.items())]
    return hashlib.sha256(json.dumps(serial, separators=(",", ":")).encode()).hexdigest()


def codim(label):
    return 0 if label == 0 else 2 if label == 2 else 1


def energy(r, beta):
    return sum(w * b for w, b in zip(((3,), (1, 2), (1, 1, 1))[r], beta))


@lru_cache(None)
def curve_assignments(beta, vertices):
    if vertices == 1:
        return ((beta,),)
    return tuple((a,) + rest
                 for a in product(*(range(b + 1) for b in beta))
                 for rest in curve_assignments(tuple(b - x for b, x in zip(beta, a)), vertices - 1))


def contract(graph, psi, coefficient, r, beta, labels, positive_metric=False):
    """Direct vertex/edge enumeration; no Lean expression or recursive evaluator."""
    genera = tuple(map(int, graph.genera()))
    fixed = [[] for _ in genera]
    for flag, label in enumerate(labels, 1):
        fixed[int(graph.vertex(flag))].append((label, int(psi.get(flag, 0))))
    answer = defaultdict(Fraction)
    for states in product(range(r + 3), repeat=len(graph.edges())):
        insertions = [items.copy() for items in fixed]
        weight = coefficient
        for (left, right), state in zip(graph.edges(), states):
            dual = 2 if state == 0 else 0 if state == 2 else state
            if state >= 3 and not positive_metric:
                weight *= -1
            insertions[int(graph.vertex(left))].append((state, int(psi.get(left, 0))))
            insertions[int(graph.vertex(right))].append((dual, int(psi.get(right, 0))))
        insertions = tuple(tuple(sorted(items)) for items in insertions)
        expected = tuple(sum(codim(s) + p for s, p in items) - g + 1 - len(items)
                         for g, items in zip(genera, insertions))
        for curves in curve_assignments(beta, len(genera)):
            if any(energy(r, b) != d for b, d in zip(curves, expected)):
                continue
            monomial = tuple(sorted(zip(genera, curves, insertions)))
            answer[monomial] += weight
    return {m: c for m, c in answer.items() if c}


def explore(payload):
    from sage.all import QQ, matrix
    from sage.version import version
    from admcycles import StableGraph, TautologicalRing, admcycles, stable_graph, tautological_ring
    require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
            "Review Sage/admcycles pins")
    require(hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA256, "BP source changed")
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices,
            admcycles.genstobasis, admcycles.FZ_conjecture_holds)), "Online lookup active")
    source = json.loads(SOURCE.read_bytes())
    data = json.loads(payload)
    require(data["schema_version"] == 1, "Unexpected Lean export version")
    names = [c["name"] for c in data["cases"]]
    require(len(names) == len(EXPECTED_CASES) and set(names) == set(EXPECTED_CASES),
            "Incomplete case coverage")
    base = TautologicalRing(2, 3, moduli="st", base_ring=QQ)

    def raw(graph):
        legs = [[] for _ in graph["genus"]]
        psi = {}
        for flag, (v, p) in enumerate(zip(graph["leg_vertices"], graph["leg_psi"]), 1):
            legs[v].append(flag)
            if p:
                psi[flag] = p
        edges = []
        for e, (ends, powers) in enumerate(zip(graph["endpoints"], graph["half_psi"])):
            flags = (4 + 2 * e, 5 + 2 * e)
            edges.append(flags)
            for flag, v, p in zip(flags, ends, powers):
                legs[v].append(flag)
                if p:
                    psi[flag] = p
        return base(StableGraph(graph["genus"], legs, edges), psi=psi)

    @lru_cache(None)
    def bp(n, assignments=6, omit_tail_corrections=False):
        result = []
        permutations = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
        for held in source["published_terms"]:
            coefficient = Fraction(*held["coefficient"]) / held["automorphism"]
            for perm in permutations[:assignments]:
                original = raw(relabel(held["graph"], perm))
                pulled = original if n == 0 else original.forgetful_pullback(list(range(4, 4 + n)))
                for term in pulled._terms.values():
                    for (kappa, psi), c in zip(term.poly.monom, term.poly.coeff):
                        require(all(not any(v) for v in kappa), "Unexpected kappa term")
                        c = QQ(c)
                        c = Fraction(int(c.numerator()), int(c.denominator()))
                        # Input is one raw monomial, so negative pullback coefficients
                        # are precisely its rational-tail corrections.
                        if omit_tail_corrections and c < 0:
                            continue
                        result.append((term.gamma, psi, coefficient * c))
        return result

    def contracted(case, **mutation):
        r, beta, n, original_labels = EXPECTED_CASES[case["name"]]
        answer = defaultdict(Fraction)
        positive = mutation.pop("positive_metric", False)
        for graph, psi, coefficient in bp(n, **mutation):
            for m, c in contract(graph, psi, coefficient, r, beta,
                                 original_labels + (2,) * n, positive).items():
                answer[m] += c
        return {m: c for m, c in answer.items() if c}

    reports, reduced_by_name, raw_by_name = [], {}, {}
    for case in data["cases"]:
        r, beta, n, labels = EXPECTED_CASES[case["name"]]
        require((case["blowups"], tuple(case["curve"]), case["additional_markings"],
                 tuple(case["labels"])) == (r, beta, n, labels), "Request changed")
        raw_exact = contracted(case)
        require(raw_exact == collect(case["symbolic_terms"]), f"Raw contraction: {case['name']}")
        low = {query_key(q["query"]): Fraction(*q["value"]) for q in case["lower_values"]}
        require(len(low) == len(case["lower_values"]), "Repeated terminal query")
        reduced = defaultdict(Fraction)
        for m, c in raw_exact.items():
            high = []
            for q in m:
                if q[0] <= 1:
                    require(q in low, "Missing lower-genus substitution")
                    c *= low[q]
                else:
                    high.append(q)
            reduced[tuple(high)] += c
        reduced = {m: c for m, c in reduced.items() if c}
        require(reduced == collect(case["genus_two_terms"]), f"Partial reconstruction: {case['name']}")
        require(all(len(m) <= 1 for m in reduced), "Nonlinear genus-two monomial")
        unknowns = [m[0] for m in reduced if m]
        require(all(q[0] == 2 and all(x <= b for x, b in zip(q[1], beta)) for q in unknowns),
                "Wrong genus or full-class support")
        at_class = [q for q in unknowns if q[1] == beta]
        smaller = [q for q in unknowns if q[1] != beta]
        require(all(energy(r, q[1]) < energy(r, beta) for q in smaller), "No strict decrease")
        constant = reduced.get((), Fraction(0))
        reports.append({"name": case["name"], "raw_monomials": len(raw_exact),
                        "affine_monomials": len(reduced), "same_class_unknowns": len(at_class),
                        "smaller_class_unknowns": len(smaller),
                        "constant": [constant.numerator, constant.denominator],
                        "raw_sha256": digest(raw_exact), "affine_sha256": digest(reduced),
                        "raw_equal": True, "partial_reconstruction_equal": True})
        raw_by_name[case["name"]] = raw_exact
        reduced_by_name[case["name"]] = reduced

    rejected = []
    for name, case_name, mutation in [
        ("positive_exceptional_metric", "f1_E_EEE", {"positive_metric": True}),
        ("missing_five_marking_assignments", "p2_line_HHH", {"assignments": 1}),
        ("missing_rational_tail_corrections", "p2_line_HHH", {"omit_tail_corrections": True})]:
        case = next(c for c in data["cases"] if c["name"] == case_name)
        require(contracted(case, **mutation) != raw_by_name[case_name], f"Mutation survived: {name}")
        rejected.append(name)
    require(raw_by_name["bl2_E1_E1E1E1"] != raw_by_name["bl2_E2_E1E1E1"],
            "Distinct equal-energy classes were identified")
    rejected.append("replace_full_curve_by_energy")

    rank_report = []
    for r, beta in sorted({(v[0], v[1]) for v in EXPECTED_CASES.values()}):
        family = [reduced_by_name[name] for name, v in EXPECTED_CASES.items() if v[:2] == (r, beta)]
        columns = sorted({m[0] for p in family for m in p if m and m[0][1] == beta})
        rows = [[QQ(p.get((q,), 0)) for q in columns] for p in family]
        rank_report.append({"blowups": r, "curve": beta, "equations": len(rows),
                            "same_class_unknowns": len(columns),
                            "rank": int(matrix(QQ, len(rows), len(columns), sum(rows, [])).rank())})
    sources = [Path(__file__).resolve(), ROOT / "scripts/SurfaceBP.lean", SOURCE]
    modules = [Path(m.__file__) for m in (admcycles, stable_graph, tautological_ring)]
    return {"schema_version": 1, "scope": "BP ancestor equations, not solved genus-two invariants",
            "sage": version, "admcycles": importlib.metadata.version("admcycles"),
            "online_lookup": False, "lean_payload_sha256": hashlib.sha256(payload).hexdigest(),
            "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in sources},
            "admcycles_module_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in modules},
            "cases": reports, "mutations_rejected": rejected, "sample_matrix_ranks": rank_report,
            "numerical_scope": "Lower-genus values are shared Lean algorithm outputs; only graph contraction and substitution are independently compared."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.lean_input:
        payload = args.lean_input.read_bytes()
    else:
        subprocess.run(["lake", "build", "surfaceBP"], cwd=ROOT, check=True, stdout=sys.stderr)
        payload = subprocess.check_output([str(ROOT / ".lake/build/bin/surfaceBP")], cwd=ROOT)
    with tempfile.TemporaryDirectory(prefix="surface-bp-sage-") as cache:
        for variable, name in (("DOT_SAGE", "sage"), ("ADMCYCLES_CACHE_DIR", "admcycles"),
                               ("MPLCONFIGDIR", "matplotlib"), ("XDG_CACHE_HOME", "xdg")):
            location = Path(cache) / name
            location.mkdir()
            os.environ[variable] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        report = explore(payload)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"cases": len(report["cases"]), "mutations_rejected": report["mutations_rejected"],
                      "output": str(args.output)}))


if __name__ == "__main__":
    main()
