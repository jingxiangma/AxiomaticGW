#!/usr/bin/env python3
"""Replay every original BP diagram and marking contribution separately.

The component sums must agree with the complete scalar report, whose existing
preflight checks the held queries and all recursive dependencies. Those checks
are diagnostics only: Lean evaluates each original component, including zeros,
then uses the proved sum identities to recover the unchanged scalar API.
"""

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from export_admcycles_certificate import rational_text
from export_plane_genus_two_scalar import (
    rational, read_report as read_scalar_report, require, scalar_namespace, vector,
)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Repeated JSON key: {key}")
        result[key] = value
    return result


def fields(value, expected, context):
    require(isinstance(value, dict) and set(value) == set(expected),
            f"Unexpected fields in {context}")


def component_sum(parts, diagrams):
    require(isinstance(parts, list) and len(parts) == diagrams,
            "Incomplete diagram coverage")
    require(all(isinstance(row, list) and len(row) == 6 for row in parts),
            "Expected every one of the six marking assignments")
    return sum((rational(q) for row in parts for q in row), Fraction(0))


def scalar_report(report):
    """Remove only the extra component data, preserving the entire original claim."""
    aggregate = copy.deepcopy(report)
    aggregate["kind"] = "axiomatic_gw.plane_genus_two_scalar"
    for row in aggregate["rows"]:
        for equation in row["equations"]:
            del equation["constant_parts"]
            for term in equation["earlier_coefficients"]:
                del term["parts"]
    return aggregate


def read_report(raw, bound):
    report = json.loads(raw, object_pairs_hook=unique_object)
    fields(report, ["schema_version", "kind", "bound", "initial", "rows"], "report")
    require(report["kind"] == "axiomatic_gw.plane_genus_two_scalar_parts",
            "Wrong component report kind")
    require(isinstance(report["rows"], list), "Expected a list of degrees")
    for row in report["rows"]:
        fields(row, ["degree", "requests", "values", "equations"], "degree")
        require(isinstance(row["equations"], list), "Expected a list of equations")
        for equation in row["equations"]:
            fields(equation, ["family", "constant", "constant_parts",
                              "earlier_coefficients", "remainder"], "equation")
            require(component_sum(equation["constant_parts"], 16)
                    == rational(equation["constant"]), "Constant components have wrong sum")
            require(isinstance(equation["earlier_coefficients"], list),
                    "Expected a list of earlier coefficients")
            for term in equation["earlier_coefficients"]:
                fields(term, ["degree", "family", "coefficient", "parts"], "coefficient")
                require(component_sum(term["parts"], 4) == rational(term["coefficient"]),
                        "Coefficient components have wrong sum")
    # Reuse the complete query, degree, seed, dependency and matrix checks.
    _, values = read_scalar_report(json.dumps(scalar_report(report)), bound)
    return report, values


def header(raw, degree, *, reuse_markings=False, proof_method="decide"):
    module = "PlaneGenusTwoScalarSymmetry" if reuse_markings else "PlaneGenusTwoScalarParts"
    imports = ["public import AxiomaticGW.Surfaces." + module]
    if proof_method == "fast":
        imports += ["public import AxiomaticGW.Surfaces.PlaneGenusTwoFirstCoefficients"]
    source = ["/-", f"Generated complete plane genus-two component replay at degree {degree}.",
            "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
            "All original diagrams and six marking assignments are checked, including zeros.",
            "These are candidate computations until this Lean module compiles.",
            "-/", "module", "",
            *imports, "",
            "@[expose] public section", "set_option Elab.async false",
            "set_option maxRecDepth 20000", "",
            "namespace AxiomaticGW." + scalar_namespace(degree),
            "open BelorousskiPandharipande", ""]
    if proof_method == "fast":
        source += ["-- Select the actual finite-vector branch before evaluating its contents.",
                   "attribute [local cbv_eval] Matrix.cons_val_zero Matrix.cons_val_succ",
                   "attribute [local cbv_eval] Matrix.cons_val_zero' Matrix.cons_val_succ'", ""]
    return source


def component_claim(name, expression, value, *, proof_method="decide"):
    require(proof_method in ("decide", "cbv", "hybrid", "fast"), "Unsupported proof method")
    first_coefficient = (proof_method == "fast" and
                         expression.startswith("planeEarlierCoefficientPart "))
    if proof_method == "hybrid":
        # CBV is effective on dimension-pruned constants. Coefficient recursion
        # needs the kernel evaluator's lazy branches, even for some zero entries.
        proof_method = "cbv" if expression.startswith("planeShiftedConstantPart ") else "decide"
    if proof_method == "fast":
        proof_method = "cbv"
    options = (["set_option maxHeartbeats 1000000 in",
                "-- Kernel replay of one complete finite graph contribution.",
                "set_option cbv.maxSteps 1000000 in"] if proof_method == "cbv" else [])
    tactic = "cbv" if proof_method == "cbv" else "decide +kernel"
    if first_coefficient:
        # The proved shortcut removes cotangent-tail recursion. Kernel reduction
        # then skips zero branches that CBV still evaluates in nested gluings.
        return options + [f"private theorem {name} : {expression} =",
                          f"    {rational_text(rational(value))} := by",
                          "  rw [← planeEarlierCoefficientPartFast_eq]",
                          "  decide +kernel"]
    return options + [f"private theorem {name} : {expression} =",
                      f"    {rational_text(rational(value))} := by {tactic}"]


def component_expression(degree, family, diagram, assignment, earlier=None):
    if earlier is None:
        return f"planeShiftedConstantPart {degree} {family} {diagram} {assignment}"
    b, j = earlier
    return f"planeEarlierCoefficientPart {degree} {family} {b} {j} {diagram} {assignment}"


def emit_component(raw, bound, degree, family, diagram, assignment, *, earlier=None,
                   proof_method="decide"):
    """A single exact component for resource pilots and coherent-forgery regressions."""
    report, _ = read_report(raw, bound)
    require(type(degree) is int and 1 <= degree <= bound, "Degree outside held bound")
    require(type(family) is int and 0 <= family < 3, "Invalid row")
    equation = report["rows"][degree - 1]["equations"][family]
    if earlier is None:
        parts = equation["constant_parts"]
    else:
        terms = [t for t in equation["earlier_coefficients"]
                 if (t["degree"], t["family"]) == earlier]
        require(len(terms) == 1, "Earlier entry is not a retained dependency")
        parts = terms[0]["parts"]
    require(type(diagram) is int and 0 <= diagram < len(parts), "Invalid diagram")
    require(type(assignment) is int and 0 <= assignment < 6, "Invalid assignment")
    source = header(raw, degree, proof_method=proof_method)
    source += component_claim("checkedComponent", component_expression(
        degree, family, diagram, assignment, earlier), parts[diagram][assignment],
        proof_method=proof_method)
    source += ["", "#print axioms checkedComponent",
               "", "end AxiomaticGW." + scalar_namespace(degree), ""]
    return "\n".join(source)


def assignment_representatives(family):
    """Candidate state-preserving assignments; Lean checks every reuse equality."""
    require(type(family) is int and 0 <= family < 3, "Invalid row")
    labels = [("H", "H", "P"), ("H", "P", "P"), ("P", "P", "P")][family]
    permutations = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (2, 0, 1), (1, 2, 0), (2, 1, 0)]
    first = {}
    result = []
    for e, permutation in enumerate(permutations):
        transported = tuple(labels[j] for j in permutation)
        result.append(first.setdefault(transported, e))
    return result


def marking_lemma(name, expression, diagrams, degree, family, earlier):
    labels = ["![.hyperplane, .hyperplane, .point]", "![.hyperplane, .point, .point]",
              "![.point, .point, .point]"][family]
    points = [3 * degree + 1, 3 * degree, 3 * degree - 1][family]
    source = [f"private theorem {name}_marking (k : Fin {diagrams}) (e f : Fin 6)",
              f"    (h : ({labels} : Fin 3 → SurfaceBasisLabel .plane) ∘",
              "      labelPermutation e =",
              f"      {labels} ∘ labelPermutation f) :",
              f"    {expression} k e = {expression} k f := by"]
    if earlier is None:
        source += [f"  exact planePointConstantPart_eq_of_labels {points} ![{degree + 1}]",
                   f"    {labels} k e f h"]
    else:
        b, j = earlier
        source += [f"  exact planePointCoefficientPart_eq_of_labels {points} {degree + 1}",
                   f"    {labels} (Sum.inr (planeCanonicalQueries {b} {j})) k e f h"]
    return source + [""]


def emit_block(name, expression, parts, complete, sum_theorem, value, *, degree=None,
               family=None, earlier=None, reuse_markings=False, proof_method="decide"):
    """Check each summand, then sum only the resulting literal rationals."""
    source = [f"private def {name}_parts : Fin {len(parts)} → Fin 6 → ℚ :=", "  !["]
    for k, row in enumerate(parts):
        entries = [rational_text(rational(q)) for q in row]
        suffix = "," if k + 1 < len(parts) else ""
        literal = "    ![" + ", ".join(entries) + "]" + suffix
        if len(literal) <= 100:
            source += [literal]
        else:
            source += ["    ![" + ", ".join(entries[:3]) + ",",
                       "      " + ", ".join(entries[3:]) + "]" + suffix]
    source += ["  ]", ""]
    representatives = assignment_representatives(family) if reuse_markings else list(range(6))
    if reuse_markings:
        source += marking_lemma(name, expression, len(parts), degree, family, earlier)
    for k, row in enumerate(parts):
        for e, q in enumerate(row):
            representative = representatives[e]
            if representative == e:
                source += component_claim(f"{name}_part_{k}_{e}", f"{expression} {k} {e}", q,
                                          proof_method=proof_method)
            else:
                source += [f"private theorem {name}_part_{k}_{e} : {expression} {k} {e} =",
                           f"    {rational_text(rational(q))} := by",
                           f"  exact ({name}_marking {k} {e} {representative} "
                           "(by decide +kernel)).trans",
                           f"    {name}_part_{k}_{representative}"]
    source += ["", f"private theorem {name}_parts_checked (k : Fin {len(parts)}) (e : Fin 6) :",
               f"    {expression} k e = {name}_parts k e := by",
               "  fin_cases k <;> fin_cases e"]
    for k in range(len(parts)):
        source += [f"  · exact {name}_part_{k}_{e}" for e in range(6)]
    source += ["", f"private theorem {name} : {complete} =",
               f"    {rational_text(rational(value))} := by",
               f"  rw [{sum_theorem}]", f"  simp_rw [{name}_parts_checked]",
               "  decide +kernel", ""]
    return source


def emit_scalars(raw, bound, degree, *, reuse_markings=False, proof_method="decide"):
    report, _ = read_report(raw, bound)
    require(type(degree) is int and 2 <= degree <= bound,
            "Separate scalars cover degrees two through the held bound")
    row = report["rows"][degree - 1]
    require(proof_method in ("decide", "cbv", "hybrid", "fast"), "Unsupported proof method")
    source = header(raw, degree, reuse_markings=reuse_markings, proof_method=proof_method)
    for i, equation in enumerate(row["equations"]):
        source += emit_block(f"constant_{i}", f"planeShiftedConstantPart {degree} {i}",
                             equation["constant_parts"], f"planeShiftedConstantFast {degree} {i}",
                             "planeShiftedConstantFast_eq_sum_parts", equation["constant"],
                             degree=degree, family=i, reuse_markings=reuse_markings,
                             proof_method=proof_method)
        for term in equation["earlier_coefficients"]:
            b, j = term["degree"], term["family"]
            source += emit_block(f"coefficient_{i}_{b}_{j}",
                                 f"planeEarlierCoefficientPart {degree} {i} {b} {j}", term["parts"],
                                 f"planeEarlierCoefficient {degree} {i} {b} {j}",
                                 "planeEarlierCoefficient_eq_sum_parts", term["coefficient"],
                                 degree=degree, family=i, earlier=(b, j),
                                 reuse_markings=reuse_markings, proof_method=proof_method)
    constants = vector([rational(e["constant"]) for e in row["equations"]])
    source += ["/-- All complete constants in HHP/HPP/PPP order. -/",
               "theorem constants (i : Fin 3) :",
               f"    planeShiftedConstantFast {degree} i = ({constants} : Fin 3 → ℚ) i := by",
               "  fin_cases i"]
    source += [f"  · exact constant_{i}" for i in range(3)]
    for index, term in enumerate(row["equations"][0]["earlier_coefficients"]):
        b, j = term["degree"], term["family"]
        coefficients = vector([rational(e["earlier_coefficients"][index]["coefficient"])
                               for e in row["equations"]])
        source += ["", "/-- The full signed coefficient of this nonzero earlier entry. -/",
                   f"theorem coefficients_{b}_{j} (i : Fin 3) :",
                   f"    planeEarlierCoefficient {degree} i {b} {j} =",
                   f"      ({coefficients} : Fin 3 → ℚ) i := by", "  fin_cases i"]
        source += [f"  · exact coefficient_{i}_{b}_{j}" for i in range(3)]
    source += ["", "end AxiomaticGW." + scalar_namespace(degree), ""]
    return "\n".join(source)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--bound", required=True, type=int)
    parser.add_argument("--degree", required=True, type=int)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--reuse-markings", action="store_true")
    parser.add_argument("--proof-method", choices=("decide", "cbv", "hybrid", "fast"),
                        default="decide", help="fast uses proved low-psi coefficients with kernel "
                        "reduction and CBV constants; "
                        "hybrid uses CBV constants and kernel coefficient reduction")
    args = parser.parse_args()
    source = emit_scalars(args.report.read_bytes(), args.bound, args.degree,
                          reuse_markings=args.reuse_markings, proof_method=args.proof_method)
    if args.check:
        require(args.output.read_text() == source, "Replay source differs")
    else:
        args.output.write_text(source)


if __name__ == "__main__":
    main()
