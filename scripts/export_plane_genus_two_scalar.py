#!/usr/bin/env python3
"""Export held plane genus-two scalar candidates to complete Lean certificates.

Python checks request coverage and exact arithmetic for useful diagnostics.
Lean separately checks every constant and every coefficient multiplying a
nonzero earlier value, then proves the entire finite table and requested claims.
Neither native computation nor this preflight is an invariant certificate.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from export_admcycles_certificate import rational_text


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value):
    require(isinstance(value, list) and len(value) == 2
            and all(type(x) is int for x in value) and value[1] > 0,
            "Expected an exact rational pair with positive denominator")
    q = Fraction(*value)
    require([q.numerator, q.denominator] == value, "Rational pair is not normalized")
    return q


def requests(degree):
    points = lambda n: [[2, 0] for _ in range(n)]
    return [{"genus": 2, "curve": [degree], "insertions": states} for states in [
        points(3 * degree + 1),
        [[1, 1]] + points(3 * degree),
        [[2, 1]] + points(max(3 * degree - 1, 0))]]


def read_report(raw, bound):
    require(type(bound) is int and bound >= 0, "Expected a nonnegative held degree bound")
    report = json.loads(raw)
    require(type(report.get("schema_version")) is int and report["schema_version"] == 1,
            "Unsupported schema")
    require(report.get("kind") == "axiomatic_gw.plane_genus_two_scalar", "Wrong report kind")
    require(type(report.get("bound")) is int and report["bound"] == bound,
            "Report does not match the independently held bound")
    initial = [rational(q) for q in report["initial"]]
    require(initial == [0, Fraction(-1, 960), 0], "Changed derived initial triple")
    rows = report["rows"]
    require(isinstance(rows, list) and len(rows) == bound, "Incomplete degree coverage")
    values = [initial]
    for d, row in enumerate(rows, 1):
        require(type(row.get("degree")) is int and row["degree"] == d,
                "Missing, repeated or reordered degree")
        require(json.dumps(row.get("requests"), sort_keys=True)
                == json.dumps(requests(d), sort_keys=True), "Changed full canonical query")
        new = [rational(q) for q in row["values"]]
        require(len(new) == 3, "Expected all three canonical values")
        expected = [(b, j) for b in range(d) for j in range(3) if values[b][j] != 0]
        equations = row["equations"]
        require(isinstance(equations, list) and len(equations) == 3,
                "Missing canonical equation")
        matrix = [[-108*d, -27*d*d+27*d+12, 27*d*d*d+9*d*d],
                  [-36, 12-36*d, 36*d*d], [0, -18, 18*d]]
        for i, equation in enumerate(equations):
            require(type(equation.get("family")) is int and equation["family"] == i,
                    "Changed equation family")
            terms = equation["earlier_coefficients"]
            require(all(type(t.get("degree")) is int and type(t.get("family")) is int
                        for t in terms), "Invalid coefficient key")
            require([(t["degree"], t["family"]) for t in terms] == expected,
                    "Incomplete, extra or reordered nonzero dependencies")
            remainder = rational(equation["constant"]) + sum(
                rational(t["coefficient"]) * values[t["degree"]][t["family"]] for t in terms)
            require(remainder == rational(equation["remainder"]), "Incorrect remainder arithmetic")
            require(sum(c * v for c, v in zip(matrix[i], new)) + remainder == 0,
                    "Candidate does not solve the complete three-row system")
        values.append(new)
    return report, values


def vector(values):
    return "![" + ", ".join(rational_text(v) for v in values) + "]"


def query_source(q):
    labels = {0: ".unit", 1: ".hyperplane", 2: ".point"}
    states = [f"⟨{labels[label]}, {power}⟩" for label, power in q["insertions"]]
    chunks = [", ".join(states[i:i+4]) for i in range(0, len(states), 4)]
    return f"⟨2, ![{q['curve'][0]}], [" + ",\n      ".join(chunks) + "]⟩"


def scalar_namespace(degree):
    return f"GenusTwoPlaneDegree{degree}Scalars"


def scalar_module(degree):
    return "AxiomaticGW.Surfaces.Fixtures." + scalar_namespace(degree)


def emit_scalars(raw, bound, degree):
    """Keep costly closed arithmetic proofs separate from inexpensive claim assembly."""
    report, _ = read_report(raw, bound)
    require(type(degree) is int and 2 <= degree <= bound,
            "Separate scalars cover degrees two through the held bound")
    row = report["rows"][degree - 1]
    source = ["/-", f"Generated complete plane genus-two scalars at degree {degree}.",
              "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
              "These are checked computations, not additional seed values.",
              "-/", "module", "",
              "public import AxiomaticGW.Surfaces.PlaneGenusTwoCertificate", "",
              "@[expose] public section", "set_option Elab.async false",
              "set_option maxRecDepth 20000", "",
              "namespace AxiomaticGW." + scalar_namespace(degree),
              "open BelorousskiPandharipande", ""]
    for i, equation in enumerate(row["equations"]):
        source += [f"private theorem constant_{i} : planeShiftedConstantFast {degree} {i} =",
                   f"    {rational_text(rational(equation['constant']))} := by decide +kernel"]
        for t in equation["earlier_coefficients"]:
            b, j = t["degree"], t["family"]
            source += [f"private theorem coefficient_{i}_{b}_{j} :",
                       f"    planeEarlierCoefficient {degree} {i} {b} {j} =",
                       f"      {rational_text(rational(t['coefficient']))} := by decide +kernel"]
    constants = vector([rational(e["constant"]) for e in row["equations"]])
    source += ["", "/-- All complete constants in HHP/HPP/PPP order. -/",
               "theorem constants (i : Fin 3) :",
               f"    planeShiftedConstantFast {degree} i = ({constants} : Fin 3 → ℚ) i := by",
               "  fin_cases i"]
    source += [f"  · exact constant_{i}" for i in range(3)]
    for index, t in enumerate(row["equations"][0]["earlier_coefficients"]):
        b, j = t["degree"], t["family"]
        coefficients = vector([rational(e["earlier_coefficients"][index]["coefficient"])
                               for e in row["equations"]])
        source += ["", "/-- The full signed coefficient of this nonzero earlier entry. -/",
                   f"theorem coefficients_{b}_{j} (i : Fin 3) :",
                   f"    planeEarlierCoefficient {degree} i {b} {j} =",
                   f"      ({coefficients} : Fin 3 → ℚ) i := by", "  fin_cases i"]
        source += [f"  · exact coefficient_{i}_{b}_{j}" for i in range(3)]
    source += ["", "end AxiomaticGW." + scalar_namespace(degree), ""]
    return "\n".join(source)


def emit(raw, bound, *, split_scalars=False):
    report, values = read_report(raw, bound)
    source = ["/-", "Generated exact plane genus-two candidates.",
              "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
              "Every scalar and the complete table are separately checked by Lean.",
              "-/", "module", "",
              "public import " + ("AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLineScalars"
                                   if bound else "AxiomaticGW.Surfaces.PlaneGenusTwoCertificate")]
    if split_scalars:
        source += ["public import " + scalar_module(d) for d in range(2, bound + 1)]
    source += ["", "@[expose] public section", "set_option Elab.async false",
              "set_option maxRecDepth 20000", "",
              "namespace AxiomaticGW.PlaneGenusTwoScalarTable", "open BelorousskiPandharipande", "",
              "/-- Candidates outside the held bound are not certified. -/",
              "def values : ℕ → Fin 3 → ℚ"]
    source += [f"  | {d} => {vector(v)}" for d, v in enumerate(values)]
    source += ["  | _ => ![0, 0, 0]", "",
               "private theorem row_0 : planeCheckCanonicalRow values 0 = true := by",
               "  decide +kernel", ""]
    for d, row in enumerate(report["rows"], 1):
        for i, equation in enumerate(row["equations"]):
            name = f"constant_{d}_{i}"
            proof = (f"GenusTwoPlaneLineScalars.constants {i}" if d == 1 else "by decide +kernel")
            if split_scalars and d > 1:
                proof = f"{scalar_namespace(d)}.constants {i}"
            source += [f"private theorem {name} : planeShiftedConstantFast {d} {i} =",
                       f"    {rational_text(rational(equation['constant']))} := {proof}"]
            for t in equation["earlier_coefficients"]:
                b, j = t["degree"], t["family"]
                name = f"coefficient_{d}_{i}_{b}_{j}"
                proof = (f"GenusTwoPlaneLineScalars.coefficients {i}"
                         if d == 1 else "by decide +kernel")
                if split_scalars and d > 1:
                    proof = f"{scalar_namespace(d)}.coefficients_{b}_{j} {i}"
                source += [f"private theorem {name} : planeEarlierCoefficient {d} {i} {b} {j} =",
                           f"    {rational_text(rational(t['coefficient']))} := {proof}"]
        constants = vector([rational(e["constant"]) for e in row["equations"]])
        names = [f"constant_row_{d}"]
        source += ["", f"private theorem constant_row_{d} (i : Fin 3) :",
                   f"    planeShiftedConstantFast {d} i = ({constants} : Fin 3 → ℚ) i := by",
                   "  fin_cases i"]
        source += [f"  · exact constant_{d}_{i}" for i in range(3)]
        for index, t in enumerate(row["equations"][0]["earlier_coefficients"]):
            b, j = t["degree"], t["family"]
            name = f"coefficient_row_{d}_{b}_{j}"
            names.append(name)
            coefficients = vector([rational(e["earlier_coefficients"][index]["coefficient"])
                                   for e in row["equations"]])
            source += ["", f"private theorem {name} (i : Fin 3) :",
                       f"    planeEarlierCoefficient {d} i {b} {j} =",
                       f"      ({coefficients} : Fin 3 → ℚ) i := by", "  fin_cases i"]
            source += [f"  · exact coefficient_{d}_{i}_{b}_{j}" for i in range(3)]
        rem = vector([rational(e["remainder"]) for e in row["equations"]])
        source += ["", f"private theorem remainder_{d} (i : Fin 3) :",
                   f"    planeScalarRemainder values {d} i = ({rem} : Fin 3 → ℚ) i := by",
                   "  norm_num [planeScalarRemainder, Fin.sum_univ_succ, values,"]
        source += ["    " + ", ".join(names[k:k+3]) + ("," if k+3 < len(names) else "]")
                   for k in range(0, len(names), 3)]
        source += ["  fin_cases i <;> norm_num [Matrix.cons_val_two]"]
        source += ["", f"private theorem row_{d} : planeCheckCanonicalRow values {d} = true := by",
                   f"  have hr : (fun i ↦ -planeScalarRemainder values {d} i) =",
                   f"      (fun i ↦ -({rem} : Fin 3 → ℚ) i) := by",
                   f"    funext i; rw [remainder_{d}]",
                   "  rw [planeCheckCanonicalRow, if_neg (by decide), decide_eq_true_eq, hr]",
                   "  decide +kernel", ""]
    source += ["/-- Every degree, including every zero entry, satisfies the original recursion. -/",
               f"theorem accepted : planeCheckCanonicalTable {bound} values = true := by",
               "  rw [planeCheckCanonicalTable, decide_eq_true_eq]", "  intro d", "  fin_cases d"]
    source += [f"  · exact row_{d}" for d in range(bound+1)]
    source += ["", "/-- All covered candidates equal the original terminating reconstruction. -/",
               f"theorem values_eq (d : ℕ) (hd : d ≤ {bound}) :",
               "    values d = planeCanonicalValues d :=",
               f"  planeCheckCanonicalTable_sound {bound} values accepted d hd", ""]
    if bound:
        source += ["/-- Incoming full requests, kept independently of the certified values. -/",
                   f"def requests : Fin {bound} → Fin 3 → SurfaceQuery .plane :=", "  !["]
        for index, row in enumerate(report["rows"]):
            source += ["    ![" + ",\n      ".join(query_source(q) for q in row["requests"])
                       + ("]" if index+1 == bound else "],")]
        source += ["  ]", "", "/-- Hold target, full degree, labels and cotangent powers fixed. -/",
                   "theorem coverage : ∀ d i, requests d i = planeCanonicalQueries (d.val + 1) i := by",
                   "  decide +kernel", "",
                   "/-- Every positive-degree output is bound to its incoming full query. -/",
                   f"theorem claims : ∀ d i, planeCheckCanonicalClaim {bound} values",
                   "    (requests d i) (values (d.val + 1) i) = true := by",
                   "  intro d i",
                   "  rw [planeCheckCanonicalClaim, accepted, Bool.and_true, decide_eq_true_eq]",
                   "  exact ⟨⟨d.val + 1, by omega⟩, i, coverage d i, rfl⟩", ""]
    source += ["end AxiomaticGW.PlaneGenusTwoScalarTable", ""]
    return "\n".join(source)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--bound", required=True, type=int,
                        help="Independently held degree bound; the release benchmark is four")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--split-scalars", action="store_true",
                        help="Write degree scalar modules beside the table in the fixtures directory")
    args = parser.parse_args()
    raw = args.report.read_bytes()
    source = emit(raw, args.bound, split_scalars=args.split_scalars)
    outputs = {args.output: source}
    if args.split_scalars:
        fixtures = Path(__file__).resolve().parents[1] / "AxiomaticGW/Surfaces/Fixtures"
        require(args.output.resolve().parent == fixtures,
                "Split scalar modules must be written to the existing fixtures directory")
        outputs.update({fixtures / (scalar_namespace(d) + ".lean"): emit_scalars(raw, args.bound, d)
                        for d in range(2, args.bound + 1)})
    for path, text in outputs.items():
        if args.check:
            require(path.read_text() == text, f"Replay source differs: {path}")
        else:
            path.write_text(text)


if __name__ == "__main__":
    main()
