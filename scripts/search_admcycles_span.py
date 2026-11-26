#!/usr/bin/env python3
"""Find and export a relation in the pinned codimension-two frame of Mbar(2,0)."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

from export_admcycles_certificate import (
    PINNED_RAW_COORDINATES_SHA256, rational, rational_text, read_report, vector,
)

REPORT = Path(__file__).resolve().parents[1] / "environments" / "admcycles-smoke-osx-arm64.json"


def coefficient(text):
    try:
        return Fraction(text)
    except (ValueError, ZeroDivisionError) as err:
        raise argparse.ArgumentTypeError(f"Invalid rational coefficient: {text}") from err


def search(request, report_path):
    from sage.all import QQ, matrix
    from sage.all import vector as sage_vector

    report, _ = read_report(report_path)
    if report["raw_coordinate_sha256"] != PINNED_RAW_COORDINATES_SHA256:
        raise ValueError("The input graph frame differs from the compiled eight-column frame")
    rows = matrix(QQ, [[rational(pair) for pair in row]
                       for row in report["arithmetic"]["fz_rows_monomial"]])
    target = sage_vector(QQ, request)
    try:
        solution = rows.solve_left(target)
    except ValueError:
        raise ValueError("Requested expression lies outside the span of the seven supplied rows") from None
    if solution * rows != target:
        raise ValueError("Sage did not recover the requested coordinates")
    return [Fraction(int(x.numerator()), int(x.denominator())) for x in solution]


def source(request, weights):
    digest = hashlib.sha256(json.dumps([str(x) for x in request]).encode()).hexdigest()
    ns = "AxiomaticGW.Research.UnmarkedGenusTwo_" + digest[:20]
    return f"""import AxiomaticGW.Tautological.Fixtures.AdmcyclesGenusTwo

namespace {ns}
open RelationCertificate AdmcyclesGenusTwo

/-- Requested coordinates in the fixed raw monomial-kappa graph order. -/
def target : Coordinates 8 := {vector([rational_text(x) for x in request])}

/-- Row weights found by exact linear algebra on the seven admcycles rows. -/
def witness : Certificate 7 := ⟨{vector([rational_text(x) for x in weights])}⟩

theorem accepted : check rows target witness = true := by decide +kernel

theorem in_span : interpret columns target ∈ relationSpan columns rows :=
  check_sound columns rows target witness accepted

theorem evaluated {{M : Type*}} [AddCommMonoid M] [Module ℚ M]
    (ev : StrataModule 2 (Fin 0) →ₗ[ℚ] M)
    (hrows : ∀ i, ev (interpret columns (rows i)) = 0) :
    ev (interpret columns target) = 0 :=
  evaluation_eq_zero columns rows target witness accepted ev hrows

#print axioms in_span
#print axioms evaluated
end {ns}
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("coordinates", nargs=8, type=coefficient, metavar="q",
                        help="eight exact integer or rational coordinates in monomial-kappa order")
    parser.add_argument("--report", type=Path, default=REPORT,
                        help="pinned admcycles smoke report, including a freshly regenerated copy")
    args = parser.parse_args()
    try:
        print(source(args.coordinates, search(args.coordinates, args.report)), end="")
    except (ImportError, ValueError, OSError) as err:
        print(f"Relation search failed: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
