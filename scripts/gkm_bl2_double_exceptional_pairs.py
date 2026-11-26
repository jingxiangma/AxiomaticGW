#!/usr/bin/env python3
"""Localize the ordered genus-two string, dilaton and own-divisor pairs in both classes 2Eᵢ."""
from gkm_regular_fraction_table import ordered_surface_frame
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report


KIND = "gkm_localization.bl2_double_exceptional_pairs"
NAMESPACE = "BlowupTwoDoubleExceptionalPairs"


def requests():
    rows = []
    for beta, divisor in (((2, 0, 0), "E1"), ((0, 2, 0), "E2")):
        for first, powers in (("unit", (0, 4)), ("unit", (1, 3)), (divisor, (0, 3))):
            labels = (first, divisor)
            rows.extend(((beta, powers, labels), (beta, powers[::-1], labels[::-1])))
    return {"X0": [], "X1": [], "X2": rows}


REQUESTS = requests()


def emit(raw):
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    incoming = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
                for c in grouped["X2"]}
    source = ordered_surface_frame(raw, [incoming[q] for q in REQUESTS["X2"]],
                                   lean_target=".blowupTwo", namespace=NAMESPACE,
                                   title="Genus-two string, dilaton and divisor pairs in both doubled exceptional curves",
                                   generator="gkm_bl2_double_exceptional_pairs.py")
    source = source.replace("public import AxiomaticGW.Surfaces.Queries",
                            "public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalPairs")
    source = source.replace("] : Array (SurfaceQuery", "] :\n    Array (SurfaceQuery")
    end = f"end AxiomaticGW.GKM.{NAMESPACE}\n"
    return source.removesuffix(end) + '''open SurfaceGenusTwoBlowupDescendants

/-- Within each axis the three marked equations are listed in both marking orders. -/
def index (axis : Fin 2) (equation : Fin 3) (last : Bool) : Fin 12 :=
  ⟨6 * axis.val + 2 * equation.val + (if last then 1 else 0), by split <;> omega⟩

private theorem covers (j : Fin 12) : ∃ axis equation last, index axis equation last = j := by
  revert j
  decide +kernel

/-- The incoming requests bind the full curve, both ordered markings and the ordinary value. -/
theorem binding (axis : Fin 2) (equation : Fin 3) (last : Bool) :
    (requests (index axis equation last), values (index axis equation last)) =
      (AxiomaticGW.BlowupTwoDoubleExceptionalPairs.request axis equation last,
       AxiomaticGW.BlowupTwoDoubleExceptionalPairs.values equation) := by
  revert axis equation last
  decide +kernel

/-- Each ordered native value agrees with the original marked descendant reconstruction. -/
theorem accepted (j : Fin 12) : CheckedDescendant 0 (requests j) (values j) := by
  obtain ⟨axis, equation, last, rfl⟩ := covers j
  exact (congrArg (fun p ↦ CheckedDescendant 0 p.1 p.2) (binding axis equation last)).mpr
    (AxiomaticGW.BlowupTwoDoubleExceptionalPairs.checked axis equation last)

/-- A single witness couples reconstruction, full-field equality, and regular specialization. -/
theorem certified (j : Fin 12) : CheckedDescendant 0 (requests j) (values j) ∧
    equivariant j = (values j : Coefficient) ∧ Specializes (equivariant j) (values j) :=
  ⟨accepted j, equivariant_eq_ordinary j, specializes j⟩

''' + end


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
