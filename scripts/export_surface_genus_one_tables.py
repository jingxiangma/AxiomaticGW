#!/usr/bin/env python3
"""Exact candidates from Chaudhuri--Das (3.1); acceptance is Lean's job.

The published intersection-number recurrence inserts four anticanonical
divisors. Lean independently contracts the 33 original graphs with four H
insertions. These are separate implementations of the same Getzler relation,
with shared geometric constants and rational inputs. No independent check of
that common mathematical foundation is claimed.
"""

import argparse
from fractions import Fraction
import hashlib
from itertools import product
import json
from math import comb

import export_surface_genus_zero_tables as rational


ROOT = rational.ROOT
BOUND = rational.BOUND
MANIFEST = ROOT / "environments/surface-genus-one-primary-tables.json"
TARGETS = {name: (target, module.replace("Zero", "One"), weights)
           for name, (target, module, weights) in rational.TARGETS.items()}


def choose(n, k):
    if n < 0:
        raise ValueError("The elliptic recurrence requires energy at least two")
    return comb(n, k) if 0 <= k <= n else 0


def positive_splits(target, beta):
    for left in product(*(range(x + 1) for x in beta)):
        right = tuple(x - y for x, y in zip(beta, left))
        if rational.energy(target, left) and rational.energy(target, right):
            yield left, right


def table(target, bound=BOUND):
    genus_zero = rational.table(target, bound)
    values = {}
    b2 = len(TARGETS[target][2])
    degree = 10 - b2
    dot = lambda a, b: rational.intersection(target, a, b)
    energy = lambda b: rational.energy(target, b)
    for beta in rational.bounded(target, bound):
        k = energy(beta)
        if k <= 1:
            # Zero class is auxiliary; positive energy-one (-1)-curves have value zero.
            # In Lean the exceptional and strict-line equations derive these values.
            values[beta] = Fraction(0)
            continue
        t1 = t2 = t3 = Fraction(0)
        for first, rest in positive_splits(target, beta):
            k1, k2 = energy(first), energy(rest)
            d12 = dot(first, rest)
            t2 += (
                choose(k - 2, k1 - 1) * 4 * k2**2 *
                (2 * k1 * k2 - k2**2 - 3 * degree * d12)
                + choose(k - 2, k1) * 2 * k2 *
                (degree * d12 * (4 * k1 + k2) + 2 * k1 * k2 * (2 * k1 - k2))
            ) * values[first] * genus_zero[rest]
            t3 -= Fraction(1, 12) * choose(k - 2, k1 - 1) * k2**2 * d12 * (
                k1**2 * (k1 - 2 * k2 - 6 * d12)
                + k2 * dot(first, first) * (4 * k1 + k2)
            ) * genus_zero[first] * genus_zero[rest]
            if values[first] == 0:
                continue
            for second, third in positive_splits(target, rest):
                k2, k3 = energy(second), energy(third)
                multinomial = choose(k - 2, k2 - 1) * choose(k - k2 - 1, k3 - 1)
                t1 += multinomial * 2 * k2 * k3**2 * dot(first, second) * (
                    (4 * k1 + k2 - 2 * k3) * dot(second, third)
                    - 3 * k2 * dot(first, third)
                ) * values[first] * genus_zero[second] * genus_zero[third]
        t4 = -Fraction(1, 12) * k**3 * ((2 + b2) * k - degree) * genus_zero[beta]
        values[beta] = (t1 + t2 + t3 + t4) / (6 * degree**2)
    return values


def payload():
    if json.loads(rational.MANIFEST.read_text()) != rational.payload():
        raise ValueError("The frozen genus-zero input does not match its recorded generator")
    cases = []
    for target in TARGETS:
        rows = []
        for curve, value in table(target).items():
            e = rational.energy(target, curve)
            rows.append({"curve": list(curve), "energy": e, "point_count": e,
                         "domain": "geometric" if e else "auxiliary_zero_class_empty_query",
                         "value": [value.numerator, value.denominator]})
        cases.append({"target": target, "genus": 1, "energy_bound": BOUND, "rows": rows})
    anchors = [
        {"target": "P2", "curve": [3], "value": [1, 1], "reference": "Getzler, Table 1"},
        {"target": "P2", "curve": [4], "value": [225, 1], "reference": "Getzler, Table 1"},
        {"target": "F1", "curve": [2, 5], "value": [240, 1],
         "reference": "Chaudhuri--Das, section 8: 5H - 3E"},
        {"target": "Bl2P2", "curve": [2, 3, 5], "value": [20, 1],
         "reference": "Chaudhuri--Das, section 8: 5H - 3E1 - 2E2"},
    ]
    for anchor in anchors:
        case = next(c for c in cases if c["target"] == anchor["target"])
        row = next(r for r in case["rows"] if r["curve"] == anchor["curve"])
        if row["value"] != anchor["value"]:
            raise ValueError(f"Published anchor mismatch: {anchor}, computed {row['value']}")
    return {
        "schema_version": 1,
        "scope": "All primary genus-one point queries through energy twelve on the three fixed targets",
        "source": {
            "title": "Elliptic Gromov-Witten Invariants of Del-Pezzo surfaces",
            "authors": ["Chitrabhanu Chaudhuri", "Nilkantha Das"],
            "url": "https://arxiv.org/abs/1901.00839v2",
            "formula": "3.1 (T1--T4), used at anticanonical energy at least two",
            "coordinate_conversion": "H,E_i coefficients; exceptional coefficients may be positive",
            "summation": "All ordered positive full-class splits; no exceptional parts omitted",
            "binomial_convention": "zero outside 0 <= k <= n; n is nonnegative",
        },
        "genus_zero_input": {
            "manifest": str(rational.MANIFEST.relative_to(ROOT)),
            "sha256": hashlib.sha256(rational.MANIFEST.read_bytes()).hexdigest(),
            "algorithm": "Kontsevich--Manin (5.18) and the recorded low-energy sector",
        },
        "published_anchors": anchors,
        "plane_reference": "https://arxiv.org/abs/alg-geom/9612004",
        "comparison_limits": [
            "Invariant candidates use only the published intersection recurrence, not a graph evaluator.",
            "Intermediate proof candidates separately contract the pinned admcycles frame; Lean checks each against its own gluing expression.",
            "It reuses the genus-zero Python generator and full-class coordinate utilities.",
            "Both elliptic calculations use Getzler's relation and the same geometric normalizations.",
            "The published recurrence uses four c1 divisors; Lean checks four H divisors.",
            "All energy-one values are zero, sharing the existing exceptional and strict-line base results.",
            "The four published anchors are fixed before kernel table acceptance.",
            "All generated rows remain candidates until exact coverage and every equation pass Lean's kernel.",
            "The auxiliary zero-class empty query is retained for recursion, not a geometric benchmark.",
            "Descendants, genus two and imported GKM CohFT data are not certified by these tables.",
        ],
        "cases": cases,
    }


def lean_module(case, digest, *, namespace=None, rational_module=None):
    from surface_genus_one_contractions import contractions, REPRESENTATIVES

    target, default_namespace, weights = TARGETS[case["target"]]
    namespace = namespace or default_namespace
    rational_module = rational_module or rational.TARGETS[case["target"]][1]
    bound = case["energy_bound"]
    intermediates = contractions(case["target"],
                                {tuple(r["curve"]): Fraction(*r["value"]) for r in case["rows"]},
                                bound=bound)
    lines = [f'''/-
Generated candidate values from Chaudhuri--Das (3.1).
The Getzler relation, rational inputs and geometric base values are shared.
Manifest SHA256: {digest}
This digest records provenance; the finite Lean check proves acceptance.
-/
module

public import AxiomaticGW.Surfaces.GenusOneCertificate
public import AxiomaticGW.Surfaces.Fixtures.{rational_module}

@[expose] public section

-- Check rows sequentially to bound kernel replay memory.
set_option Elab.async false

namespace AxiomaticGW.{namespace}

open SurfaceGenusOne

/-- Candidate elliptic point values, keyed by every effective curve coordinate. -/
def values (beta : SurfaceTarget.{target}.Curve) : ℚ :=
  match {', '.join('beta ' + str(i) for i in range(len(weights)))} with
''']
    for row in sorted(case["rows"], key=lambda r: r["curve"]):
        if row["value"][0]:
            pattern = ", ".join(map(str, row["curve"]))
            lines.append(f"  | {pattern} => {rational.lean_rational(row['value'])}\n")
    lines.append("  | " + ", ".join("_" for _ in weights) + " => 0\n\n")
    lines.append(f'''/-- Reuse the same complete full-class requests as the rational table. -/
def classes : List SurfaceTarget.{target}.Curve := {rational_module}.classes

theorem covers : classes.toFinset = SurfaceTarget.{target}.bounded {bound} :=
  {rational_module}.covers

''')
    for i, row in enumerate(case["rows"]):
        curve = "![" + ", ".join(map(str, row["curve"])) + "]"
        steps = []
        if row["energy"] > 1:
            for kind, value in zip(REPRESENTATIVES, intermediates[tuple(row["curve"])]):
                name = f"row_{i}_{kind}"
                steps.append(name)
                number = rational.lean_rational((value.numerator, value.denominator))
                lines.append(f'''private theorem {name} :
    dimensionPrunedEval .{target} {rational_module}.values
      (fun gamma ↦ if SurfaceTarget.{target}.effective.energy gamma < {row['energy']}
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .{kind}) (by omega) {curve} {row['energy'] - 2}
      (GetzlerGraphs.reconstructionLabels .{target}) = {number} := by
  decide +kernel

''')
        lines.append(f"private theorem row_{i} :\n"
                     f"    checkValue .{target} {rational_module}.values values {curve} = true := by\n")
        if steps:
            lines.append(f"  have he : SurfaceTarget.{target}.effective.energy {curve} = {row['energy']} :=\n"
                         "    by decide +kernel\n"
                         "  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]\n"
                         f"  change ({rational.lean_rational(row['value'])} : ℚ) = _\n"
                         "  simp only [orbitReconstructionStep, he, Nat.reduceSub,\n"
                         + "    " + ", ".join(steps[:4]) + ",\n"
                         + "    " + ", ".join(steps[4:]) + "]\n"
                         "  norm_num\n\n")
        else:
            lines.append("  decide +kernel\n\n")
    lines.append(f'''set_option maxRecDepth 4096 in
/-- Every elliptic equation is checked, including all vanishing classes. -/
theorem rows_checked :
    classes.all (checkValue .{target} {rational_module}.values values) = true := by
  simp only [classes, {rational_module}.classes, List.all_cons, List.all_nil,
''')
    for start in range(0, len(case["rows"]), 8):
        names = ", ".join(f"row_{i}" for i in range(start, min(start + 8, len(case["rows"]))))
        lines.append(f"    {names},\n")
    lines.append(f'''    Bool.and_true]

/-- Kernel replay checks both genera throughout the unchanged held bound. -/
theorem accepted : checkBoundedValues .{target} {bound} {rational_module}.values values = true := by
  apply checkEnumeratedValues_sound .{target} {bound} classes {rational_module}.values values
  rw [checkEnumeratedValues, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨{rational_module}.accepted, covers, rows_checked⟩

/-- Every covered candidate agrees with the original terminating elliptic evaluator. -/
theorem values_eq (beta : SurfaceTarget.{target}.Curve)
    (hbound : SurfaceTarget.{target}.effective.energy beta ≤ {bound}) :
    values beta = pointValue .{target} beta :=
  checkBoundedValues_sound .{target} {bound} {rational_module}.values values accepted beta hbound

end AxiomaticGW.{namespace}
''')
    return "".join(lines)


def outputs():
    report = payload()
    encoded = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    digest = hashlib.sha256(encoded.encode()).hexdigest()
    files = {MANIFEST: encoded}
    for case in report["cases"]:
        module = TARGETS[case["target"]][1]
        files[ROOT / f"AxiomaticGW/Surfaces/Fixtures/{module}.lean"] = lean_module(case, digest)
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check deterministic frozen output")
    args = parser.parse_args()
    for path, content in outputs().items():
        if args.check:
            if not path.exists() or path.read_text() != content:
                raise SystemExit(f"Frozen output mismatch: {path.relative_to(ROOT)}")
        else:
            path.write_text(content)
        print(("checked " if args.check else "wrote ") + str(path.relative_to(ROOT)))


if __name__ == "__main__":
    main()
