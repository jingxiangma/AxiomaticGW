#!/usr/bin/env python3
"""Exact candidates from Kontsevich--Manin (5.18); acceptance is Lean's job.

This implementation uses the published intersection-number recurrence directly,
not the Lean graph evaluator or the existing Python/Sage graph expansion. The
low-energy values are shared geometric normalizations and prior base cases;
this comparison does not independently test that initial package. Both paths
ultimately use WDVV. All zeros and all effective coordinates are retained.
"""

import argparse
from fractions import Fraction
import hashlib
from itertools import product
import json
from math import comb
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BOUND = 12
MANIFEST = ROOT / "environments/surface-genus-zero-primary-tables.json"
TARGETS = {
    "P2": ("plane", "GenusZeroPlaneTable", (3,)),
    "F1": ("hirzebruchOne", "GenusZeroF1Table", (1, 2)),
    "Bl2P2": ("blowupTwo", "GenusZeroBl2Table", (1, 1, 1)),
}


def energy(target, curve):
    weights = TARGETS[target][2]
    if len(curve) != len(weights) or any(type(x) is not int or x < 0 for x in curve):
        raise ValueError("Expected every nonnegative integral effective coordinate")
    return sum(x * w for x, w in zip(curve, weights))


def bounded(target, bound=BOUND):
    if type(bound) is not int or bound < 0:
        raise ValueError("Expected a nonnegative integral energy bound")
    weights = TARGETS[target][2]
    curves = product(*(range(bound // w + 1) for w in weights))
    return sorted((b for b in curves if energy(target, b) <= bound),
                  key=lambda b: (energy(target, b), b))


def lattice(target, curve):
    """Coefficients in H,E_i, including positive exceptional coefficients."""
    energy(target, curve)  # Validate shape before coordinate conversion.
    if target == "P2":
        return curve
    if target == "F1":
        a, b = curve
        return b, a - b
    a, b, c = curve
    return c, a - c, b - c


def intersection(target, left, right):
    a, b = lattice(target, left), lattice(target, right)
    return a[0] * b[0] - sum(x * y for x, y in zip(a[1:], b[1:]))


def choose(n, k):
    if n < 0:
        raise ValueError("The published recurrence is used only at energy at least four")
    return comb(n, k) if 0 <= k <= n else 0


def low_energy(target, curve):
    if energy(target, curve) > 3:
        raise ValueError("Only the explicitly audited low-energy sector is supplied")
    nonzero = {
        "P2": {(1,)},
        "F1": {(1, 0), (0, 1), (1, 1)},
        "Bl2P2": {(1, 0, 0), (0, 1, 0), (0, 0, 1),
                   (1, 0, 1), (0, 1, 1), (1, 1, 1)},
    }
    return Fraction(int(curve in nonzero[target]))


def table(target, bound=BOUND):
    values = {}
    for beta in bounded(target, bound):
        total_energy = energy(target, beta)
        if total_energy <= 3:
            values[beta] = low_energy(target, beta)
            continue
        value = Fraction(0)
        # Every ordered positive splitting is retained, including exceptional parts.
        for left in product(*(range(x + 1) for x in beta)):
            right = tuple(x - y for x, y in zip(beta, left))
            e1, e2 = energy(target, left), energy(target, right)
            if e1 == 0 or e2 == 0:
                continue
            h1, h2 = lattice(target, left)[0], lattice(target, right)[0]
            weight = intersection(target, left, right) * h1 * (
                h2 * choose(total_energy - 4, e1 - 2)
                - h1 * choose(total_energy - 4, e1 - 1))
            value += values[left] * values[right] * weight
        values[beta] = value
    return values


def payload():
    cases = []
    for target in TARGETS:
        rows = []
        for curve, value in table(target).items():
            e = energy(target, curve)
            rows.append({"curve": list(curve), "energy": e, "point_count": max(e - 1, 0),
                         "domain": "geometric" if e else "auxiliary_zero_class_empty_query",
                         "value": [value.numerator, value.denominator]})
        cases.append({"target": target, "genus": 0, "energy_bound": BOUND, "rows": rows})
    return {
        "schema_version": 1,
        "scope": "All primary genus-zero point queries through energy twelve on the three fixed targets",
        "source": {"title": "Gromov-Witten classes, quantum cohomology, and enumerative geometry",
                   "authors": ["Maxim Kontsevich", "Yuri Manin"],
                   "url": "https://arxiv.org/abs/hep-th/9402147",
                   "formula": "5.18, used at anticanonical energy at least four",
                   "archive_sha256": "21415c4dc2dde4a7e4caacac53bf921f55a2ecc06e5daae2d20cfc807e124b11",
                   "coordinate_conversion": "H,E_i coefficients; exceptional coordinates may be positive",
                   "binomial_convention": "zero outside 0 <= k <= n; n is nonnegative"},
        "comparison_limits": [
            "The Python recurrence does not import or reuse the Lean graph evaluator.",
            "Both mathematical calculations ultimately use WDVV.",
            "Energy at most three uses the shared normalized line, exceptional, ruling and strict-line base cases; other values in that sector are zero.",
            "Generated data are candidates until the Lean checker accepts every class; hashes do not prove mathematical acceptance.",
            "Higher genera and descendant benchmarks are not covered."],
        "cases": cases,
    }


def lean_rational(value):
    numerator, denominator = value
    return str(numerator) if denominator == 1 else f"({numerator} / {denominator} : ℚ)"


def lean_module(case, digest, *, namespace=None):
    target, default_namespace, weights = TARGETS[case["target"]]
    namespace = namespace or default_namespace
    bound = case["energy_bound"]
    header = f'''/-
Generated candidate values from the published Kontsevich--Manin formula (5.18).
The low-energy package is shared with the existing base cases.
Manifest SHA256: {digest}
This digest records provenance; the finite Lean check proves acceptance.
-/
module

public import AxiomaticGW.Surfaces.GenusZeroCertificate

@[expose] public section

-- Check rows sequentially to bound kernel replay memory.
set_option Elab.async false

namespace AxiomaticGW.{namespace}

open SurfaceGenusZero

/-- Candidate point values, keyed by every effective curve coordinate. -/
def values (beta : SurfaceTarget.{target}.Curve) : ℚ :=
  match {', '.join('beta ' + str(i) for i in range(len(weights)))} with
'''
    lines = [header]
    for row in sorted(case["rows"], key=lambda r: r["curve"]):
        if row["value"][0]:
            pattern = ", ".join(map(str, row["curve"]))
            lines.append(f"  | {pattern} => {lean_rational(row['value'])}\n")
    lines.append("  | " + ", ".join("_" for _ in weights) + " => 0\n\n")
    lines.append(f"/-- Explicit full-coordinate requests, including every zero value. -/\n")
    lines.append(f"def classes : List SurfaceTarget.{target}.Curve :=\n  [")
    lines.append(",\n   ".join("![" + ", ".join(map(str, row["curve"])) + "]" for row in case["rows"]))
    lines.append("]\n\n")
    key = "\n      + ".join(
        [f"SurfaceTarget.{target}.effective.energy beta * {(bound + 1) ** len(weights)}"] +
        [f"beta {i} * {(bound + 1) ** (len(weights) - i - 1)}" for i in range(len(weights))])
    lines.append(f'''/-- Literal tuples cover exactly the original complete bounded enumeration. -/
theorem covers : classes.toFinset = SurfaceTarget.{target}.bounded {bound} := by
  -- Adjacent increasing keys prove distinctness without pairwise function comparison.
  let code (beta : SurfaceTarget.{target}.Curve) : ℕ :=
    {key}
  have hs : (classes.map code).IsChain (· < ·) := by decide +kernel
  have hn : classes.Nodup := List.Nodup.of_map code hs.pairwise.nodup
  have hi : ∀ beta ∈ classes, SurfaceTarget.{target}.effective.energy beta ≤ {bound} := by
    decide +kernel
  apply Finset.eq_of_subset_of_card_le
  · intro beta hb
    rw [SurfaceTarget.bounded_eq, SurfaceTarget.{target}.effective.mem_bounded]
    exact hi beta (List.mem_toFinset.mp hb)
  · rw [List.toFinset_card_of_nodup hn]
    decide +kernel

''')
    for i, row in enumerate(case["rows"]):
        curve = "![" + ", ".join(map(str, row["curve"])) + "]"
        lines.append(f"private theorem row_{i} : checkValue .{target} values {curve} = true := by\n"
                     "  decide +kernel\n\n")
    lines.append(f'''set_option maxRecDepth 4096 in
/-- Every candidate equation is checked on literal tuples, including all zeros. -/
theorem rows_checked : classes.all (checkValue .{target} values) = true := by
  simp only [classes, List.all_cons, List.all_nil,
''')
    for start in range(0, len(case["rows"]), 8):
        names = ", ".join(f"row_{i}" for i in range(start, min(start + 8, len(case["rows"]))))
        lines.append(f"    {names},\n")
    lines.append(f'''    Bool.and_true]

/-- Kernel replay checks every class in the held bound. -/
theorem accepted : checkBoundedValues .{target} {bound} values = true := by
  apply checkEnumeratedValues_sound .{target} {bound} classes values
  rw [checkEnumeratedValues, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨covers, rows_checked⟩

/-- Every covered candidate agrees with the original terminating evaluator. -/
theorem values_eq (beta : SurfaceTarget.{target}.Curve)
    (hbound : SurfaceTarget.{target}.effective.energy beta ≤ {bound}) :
    values beta = pointValue .{target} beta :=
  checkBoundedValues_sound .{target} {bound} values accepted beta hbound

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
