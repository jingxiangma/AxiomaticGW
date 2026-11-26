#!/usr/bin/env python3
"""Explore the shifted plane BP system without claiming a uniform Lean recurrence.

The polynomial matrix is derived by distributing labelled primary points with
multinomial weights over the four genus-two-containing BP diagrams. For a
single psi class, its forgetful pullback has the original term and a negative
rational tail carrying a nonempty set of the added points (BP Section 3.2).
All lower components relevant to a one-degree shift have degree zero or one.

The finite native rows use the universally proved Lean coefficient evaluator.
Seven rows additionally use admcycles' actual forgetful pullback and an
incidence-based contraction. These paths share the held BP relation and plane
normalization; they do not independently certify their geometric validity.
The HHP/HPP/PPP matrix, canonical support, determinant and exact block solver
now have Lean proofs. This does not provide the lower-degree recursive evaluator.
"""
import argparse
import copy
from fractions import Fraction
import hashlib
import importlib.metadata
import itertools
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
from export_admcycles_certificate import require
from explore_surface_bp import SOURCE, SOURCE_SHA256, codim, contract
from explore_normalized_surface_bp import ancestor, matrices

ROOT = Path(__file__).resolve().parents[1]
REQUESTS = {
    "d1_HHH": (2, 1, 5, (1, 1, 1)),
    "d1_HHP": (2, 1, 4, (1, 1, 2)),
    "d1_HPP": (2, 1, 3, (1, 2, 2)),
    "d1_PPP": (2, 1, 2, (2, 2, 2)),
    "same_d2_HHP": (2, 2, 4, (1, 1, 2)),
    "same_d2_HPP": (2, 2, 3, (1, 2, 2)),
    "same_d2_PPP": (2, 2, 2, (2, 2, 2)),
    "d2_HHP": (3, 2, 7, (1, 1, 2)),
    "d2_HPP": (3, 2, 6, (1, 2, 2)),
    "d2_PPP": (3, 2, 5, (2, 2, 2)),
}


def expected_columns(degree):
    return [{"genus": 2, "curve": [degree], "insertions": sorted(items)} for items in
            ([[2, 0]] * (3 * degree + 1),
             [[1, 1]] + [[2, 0]] * (3 * degree),
             [[2, 1]] + [[2, 0]] * (3 * degree - 1))]


def validate_payload(data):
    require(data.get("schema_version") == 1, "Unknown shifted schema")
    cases = data["cases"]
    names = [c["name"] for c in cases]
    require(len(names) == len(REQUESTS) and set(names) == set(REQUESTS), "Request coverage changed")
    out = {}
    for case in cases:
        source, degree, n, labels = REQUESTS[case["name"]]
        require((case["source_curve"], case["variable_curve"], case["additional_markings"],
                 case["labels"]) == ([source], [degree], n, list(labels)), "Shifted request changed")
        require(case["columns"] == expected_columns(degree), "Full query columns changed")
        values = case["coefficients"]
        require(len(values) == 3, "Missing canonical column")
        require(all(isinstance(v, list) and len(v) == 2 and
                    all(type(x) is int for x in v) and v[1] > 0 for v in values),
                "Invalid exact coefficient")
        out[case["name"]] = [Fraction(*v) for v in values]
    return out


# This symbolic computation has no degree fitting. At each rational vertex,
# dimension fixes its point count; n! / (n-L)! counts the remaining placements.
def pullback_graphs(t, omit_corrections=False):
    """The one-psi signed pullback, with an identified nonempty new tail."""
    g = copy.deepcopy(t['graph'])
    yield (g, 1, None)
    if omit_corrections:
        return
    for (i, p) in enumerate(g['leg_psi']):
        if p:
            assert p == 1
            h = copy.deepcopy(g)
            v = h['leg_vertices'][i]
            w = len(h['genus'])
            h['genus'].append(0)
            h['leg_vertices'][i] = w
            h['leg_psi'][i] = 0
            h['endpoints'].append([v, w])
            h['half_psi'].append([0, 0])
            yield (h, -1, w)
    for (e, pair) in enumerate(g['half_psi']):
        for (b, p) in enumerate(pair):
            if p:
                assert p == 1
                h = copy.deepcopy(g)
                v = h['endpoints'][e][b]
                w = len(h['genus'])
                h['genus'].append(0)
                h['endpoints'][e][b] = w
                h['half_psi'][e][b] = 0
                h['endpoints'].append([v, w])
                h['half_psi'].append([0, 0])
                yield (h, -1, w)

def normalized_symbolic(R, d, fixed, k):
    """String, dilaton and divisor on a genus-two component, columns N,H,P."""
    out = [R.zero()] * 3
    prim = [b for (b, p) in fixed if p == 0]
    ps = [b for (b, p) in fixed if p == 1]
    assert len(ps) <= 1 and all((p <= 1 for (b, p) in fixed))
    h = prim.count(1)
    p = k + prim.count(2)
    u = prim.count(0)
    if not ps:
        if not u and p == 3 * d + 1:
            out[0] = d ** h
    elif u:
        if u == 1 and ps[0] != 0 and (p + (ps[0] == 2) == 3 * d + 1):
            out[0] = d ** (h + (ps[0] == 1))
    elif ps[0] == 0:
        if p == 3 * d + 1:
            out[0] = (2 + h + p) * d ** h
    elif ps[0] == 1:
        if p == 3 * d:
            out[1] = d ** h
            if h:
                out[0] = h * d ** (h - 1)
    elif ps[0] == 2:
        if p == 3 * d - 1:
            out[2] = d ** h
    return out

def symbolic_row(R, d, source, labels, shift, omit_corrections=False):
    """Dimension selects the point distribution, without interpolating degree values."""
    require(shift in (0, 1), "Unsupported symbolic class shift")
    n = 3 * (d + shift) + 2 - sum(map(codim, labels))
    ans = [R.zero()] * 3
    from sage.all import QQ
    for t in source['published_terms']:
        if 2 not in t['graph']['genus']:
            continue
        coeff = QQ(t['coefficient'][0]) / t['coefficient'][1] / t['automorphism']
        for (g, sign, new) in pullback_graphs(t, omit_corrections):
            G = g['genus']
            main = G.index(2)
            V = len(G)
            assignments = ([tuple(int(i == j) for i in range(V))
                            for j in range(V) if j != main] if shift == 1 else [(0,) * V])
            for perm in itertools.permutations(range(3)):
                fixed = [[] for _ in G]
                for i in range(3):
                    fixed[g['leg_vertices'][i]].append((labels[perm[i]], g['leg_psi'][i]))
                for states in itertools.product(range(3), repeat=len(g['endpoints'])):
                    ins = [x[:] for x in fixed]
                    for ((u, v), (p, q), b) in zip(g['endpoints'], g['half_psi'], states):
                        ins[u].append((b, p))
                        ins[v].append((2 - b, q))
                    for degrees in assignments:
                        ks = []
                        valid = True
                        for (v, items) in enumerate(ins):
                            k = (3 * (d if v == main else degrees[v]) + G[v] - 1 + len(items)
                                 - sum(codim(b) + p for b, p in items))
                            ks.append(k)
                            if v != main:
                                assert all((p == 0 for (b, p) in items))
                                if k < 0:
                                    valid = False
                                    break
                                if new == v and k == 0:
                                    valid = False
                                    break
                                if degrees[v] == 0:
                                    if k + len(items) != 3:
                                        valid = False
                                        break
                                elif (any(b == 0 for b, p in items)
                                      or k + sum(b == 2 for b, p in items) != 2):
                                    valid = False
                                    break
                        if not valid:
                            continue
                        assert sum(ks) == n
                        L = sum((int(k) for (v, k) in enumerate(ks) if v != main))
                        weight = R.one()
                        for j in range(L):
                            weight *= n - j
                        weight /= math.prod(math.factorial(int(k))
                                            for v, k in enumerate(ks) if v != main)
                        vec = normalized_symbolic(R, d, ins[main], ks[main])
                        for (i, x) in enumerate(vec):
                            ans[i] += coeff * sign * weight * x
    return ans


def independent_rows(source, selected):
    """Actual admcycles pullback followed by finite incidence contraction."""
    from sage.all import QQ
    from admcycles import StableGraph, TautologicalRing
    ring = TautologicalRing(2, 3, moduli="st", base_ring=QQ)
    calibration = matrices()
    # The proved first-calibration support vanishes above energy three.
    for degree in (2, 3):
        calibration[0, (degree,)] = {(a, b): Fraction(0) for a in range(3) for b in range(3)}
    pulled = {}
    answer = {}
    for name in selected:
        source_degree, degree, n, labels = REQUESTS[name]
        if n not in pulled:
            terms = []
            for held in source["published_terms"]:
                g = held["graph"]
                if 2 not in g["genus"]:
                    continue
                legs = [[] for _ in g["genus"]]
                psi = {}
                for flag, (v, p) in enumerate(zip(g["leg_vertices"], g["leg_psi"]), 1):
                    legs[v].append(flag)
                    if p:
                        psi[flag] = p
                edges = []
                for e, (ends, powers) in enumerate(zip(g["endpoints"], g["half_psi"])):
                    flags = (4 + 2 * e, 5 + 2 * e)
                    edges.append(flags)
                    for flag, v, p in zip(flags, ends, powers):
                        legs[v].append(flag)
                        if p:
                            psi[flag] = p
                original = ring(StableGraph(g["genus"], legs, edges), psi=psi)
                expansion = original.forgetful_pullback(list(range(4, 4 + n)))
                weight = Fraction(*held["coefficient"]) / held["automorphism"]
                for term in expansion._terms.values():
                    for (kappa, powers), c in zip(term.poly.monom, term.poly.coeff):
                        require(all(not any(v) for v in kappa), "Unexpected kappa")
                        c = QQ(c)
                        terms.append((term.gamma, powers,
                                      weight * Fraction(int(c.numerator()), int(c.denominator()))))
            pulled[n] = terms
        columns = [("descendant", 2, (degree,), tuple(map(tuple, q["insertions"])))
                   for q in expected_columns(degree)]
        row = [Fraction(0)] * 3
        for perm in itertools.permutations(range(3)):
            assigned = tuple(labels[i] for i in perm) + (2,) * n
            for graph, psi, weight in pulled[n]:
                for monomial, c in contract(graph, psi, weight, 0, (source_degree,), assigned).items():
                    high = [q for q in monomial if q[0] == 2]
                    require(len(high) == 1, "Expected one genus-two component")
                    normalized = ancestor(0, high[0], calibration)
                    coefficients = [normalized.get((q,), Fraction(0)) for q in columns]
                    if not any(coefficients):
                        continue
                    for q in monomial:
                        if q[0] == 2:
                            continue
                        genus, (beta,), insertions = q
                        require(genus == 0 and beta in (0, 1) and all(p == 0 for _, p in insertions),
                                "Unexpected rational component in shifted coefficient")
                        states = [b for b, _ in insertions]
                        if beta == 0:
                            c *= int(len(states) == 3 and sum(map(codim, states)) == 2)
                        else:
                            c *= int(0 not in states and states.count(2) == 2)
                    row = [x + c * y for x, y in zip(row, coefficients)]
        answer[name] = row
    return answer


def rat(value):
    if not isinstance(value, Fraction):
        value = Fraction(int(value.numerator()), int(value.denominator()))
    return [value.numerator, value.denominator]


def compare(payload):
    from sage.all import QQ, PolynomialRing, matrix
    from sage.version import version
    from admcycles import admcycles
    require("DOT_SAGE" in os.environ, "Use the fresh-cache worker")
    (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir(exist_ok=True)
    require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
            "Review Sage/admcycles pins")
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices,
            admcycles.genstobasis, admcycles.FZ_conjecture_holds)), "Online lookup active")
    require(hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA256, "BP source changed")
    source = json.loads(SOURCE.read_bytes())
    native = validate_payload(json.loads(payload))
    R = PolynomialRing(QQ, "d")
    d = R.gen()
    polynomials = {}
    for shift in (0, 1):
        for name, labels in (("HHH", (1, 1, 1)), ("HHP", (1, 1, 2)),
                             ("HPP", (1, 2, 2)), ("PPP", (2, 2, 2))):
            polynomials[shift, name] = symbolic_row(R, d, source, labels, shift)
    for name, (source_degree, degree, _, _) in REQUESTS.items():
        expected = polynomials[source_degree - degree, name.split("_")[-1]]
        require(native[name] == [Fraction(*rat(p(degree))) for p in expected],
                f"Native/symbolic coefficient mismatch: {name}")
    selected = [name for name in REQUESTS if not name.startswith("d2_")]
    independent = independent_rows(source, selected)
    require(all(native[name] == independent[name] for name in selected), "admcycles mismatch")
    M = matrix(R, [polynomials[1, name] for name in ("HHP", "HPP", "PPP")])
    require(M.det() == 7776 * d, "Changed symbolic determinant")
    require(all(not p for name in ("HHP", "HPP", "PPP") for p in polynomials[0, name]),
            "Unexpected input-class variable")
    # The signed pullback correction is tested independently of the native payload.
    changed = symbolic_row(R, d, source, (1, 1, 2), 1, omit_corrections=True)
    require(changed != polynomials[1, "HHP"], "Missing pullback correction went undetected")
    files = [Path(__file__), ROOT / "scripts/GenusTwoShifted.lean", SOURCE,
             ROOT / "AxiomaticGW/Surfaces/PointPullbackContraction.lean",
             ROOT / "AxiomaticGW/Surfaces/GenusTwoPointCoefficients.lean",
             ROOT / "AxiomaticGW/Surfaces/PlaneNormalization.lean",
             ROOT / "AxiomaticGW/Surfaces/PlaneGenusTwoCoefficients.lean",
             ROOT / "AxiomaticGW/Coefficients/WeightedCurveSplitting.lean",
             ROOT / "AxiomaticGW/Surfaces/GenusTwoCoefficientSupport.lean",
             ROOT / "AxiomaticGW/Surfaces/GenusTwoRemainder.lean",
             ROOT / "AxiomaticGW/Surfaces/PlaneGenusTwoRemainder.lean",
             ROOT / "AxiomaticGW/Surfaces/PrimaryPointPullback.lean",
             ROOT / "AxiomaticGW/Surfaces/GenusTwoPrimaryPoints.lean",
             ROOT / "AxiomaticGW/Surfaces/GenusTwoPointTails.lean",
             ROOT / "AxiomaticGW/Surfaces/GenusTwoZeroRemainder.lean",
             ROOT / "AxiomaticGW/Surfaces/PlanePointNormalization.lean",
             ROOT / "AxiomaticGW/Surfaces/PlanePointContractions.lean",
             ROOT / "AxiomaticGW/Surfaces/PlaneMixedPointContractions.lean",
             ROOT / "AxiomaticGW/Surfaces/PlaneSourceDegree.lean",
             ROOT / "AxiomaticGW/Coefficients/RenamedCoefficient.lean",
             ROOT / "AxiomaticGW/Surfaces/PlaneCanonicalComponents.lean",
             ROOT / "AxiomaticGW/Surfaces/PlaneMixedRows.lean",
             ROOT / "AxiomaticGW/Surfaces/PlaneHyperplaneRow.lean",
             ROOT / "AxiomaticGW/Surfaces/PlaneShiftedSystem.lean",
             ROOT / "AxiomaticGW/Coefficients/CollectedTerms.lean",
             ROOT / "AxiomaticGW/Surfaces/PlaneShiftedRemainder.lean",
             ROOT / "AxiomaticGW/Surfaces/PlaneShiftedStep.lean",
             ROOT / "scripts/explore_surface_bp.py", ROOT / "scripts/explore_normalized_surface_bp.py"]
    return {
        "schema_version": 1,
        "input_sha256": hashlib.sha256(payload).hexdigest(),
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in files},
        "sage": version, "admcycles": importlib.metadata.version("admcycles"),
        "native_rows": len(native), "admcycles_rows": len(independent),
        "columns": ["N_d", "H_d", "P_d"],
        "matrix_polynomials": [[[rat(c) for c in p.list()] for p in row] for row in M.rows()],
        "determinant_coefficients": [rat(c) for c in M.det().list()],
        "same_class_mixed_rows_zero": True,
        "rows": [{"name": name, "coefficients": [rat(c) for c in native[name]],
                  "symbolic_equal": True, "admcycles_equal": name in independent} for name in REQUESTS],
        "missing_signed_correction_detected": True,
        "proof_boundary": {
            "general_lean_coefficient_equality": True,
            "recursive_signed_point_compression_proved_in_lean": True,
            "plane_calibration_tail_cancellation_proved_in_lean": True,
            "plane_component_class_pruning_proved_in_lean": True,
            "effective_remainder_recursion_proved_in_lean": True,
            "plane_one_degree_rational_complement_proved_in_lean": True,
            "closed_primary_point_placements_proved_in_lean": True,
            "plane_one_psi_one_degree_remainder_formula_proved_in_lean": True,
            "plane_one_psi_zero_remainder_formula_proved_in_lean": True,
            "plane_one_psi_canonical_normalization_proved_in_lean": True,
            "uniform_ppp_row_proved_in_lean": True,
            "ppp_one_degree_remainder_support_proved_in_lean": True,
            "mixed_rational_complement_formulas_proved_in_lean": True,
            "mixed_rows_source_degree_cancellation_proved_in_lean": True,
            "mixed_rows_strict_source_degree_support_proved_in_lean": True,
            "uniform_hpp_row_proved_in_lean": True,
            "hpp_canonical_support_proved_in_lean": True,
            "hpp_lower_degree_after_canonical_block_proved_in_lean": True,
            "uniform_hhp_row_proved_in_lean": True,
            "hhp_canonical_support_proved_in_lean": True,
            "mixed_rows_lower_degree_after_canonical_block_proved_in_lean": True,
            "uniform_symbolic_compression_proved_in_lean": True,
            "uniform_symbolic_compression_scope": "Positive-degree HHP/HPP/PPP canonical block only",
            "uniform_shifted_determinant_proved_in_lean": True,
            "exact_shifted_block_solver_proved_in_lean": True,
            "collected_remainder_strict_decrease_proved_in_lean": True,
            "solved_step_from_original_geometry_proved_in_lean": True,
            "canonical_step_uniqueness_from_lower_degrees_proved_in_lean": True,
            "lower_degree_recursive_evaluation_proved_in_lean": False,
            "complete_reconstruction_or_new_invariant": False,
            "geometric_validity_independently_certified": False,
            "shared_inputs": "BP source diagrams, primary plane conventions, genus-zero line value, calibration support",
            "next": "Normalize and evaluate the lower-degree remainder, then prove finite-seed reconstruction, termination, soundness and uniqueness."
        }
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if not args.worker:
        with tempfile.TemporaryDirectory(prefix="gw-plane-shift-") as cache:
            env = os.environ.copy()
            env.update(DOT_SAGE=cache, XDG_CACHE_HOME=cache, MPLCONFIGDIR=cache)
            raise SystemExit(subprocess.run([sys.executable, "-B", str(Path(__file__).resolve()),
                "--worker", "--input", str(args.input.resolve()), "--output", str(args.output.resolve())],
                env=env).returncode)
    report = compare(args.input.read_bytes())
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"native_rows": report["native_rows"], "admcycles_rows": report["admcycles_rows"],
                      "determinant": "7776*d", "uniform_lean_reconstruction": False}))


if __name__ == "__main__":
    main()
