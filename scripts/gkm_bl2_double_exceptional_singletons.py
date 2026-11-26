#!/usr/bin/env python3
"""Localize all five dimension-compatible genus-two singleton labels on each doubled exceptional axis."""
from gkm_regular_fraction_table import ordered_surface_frame
from gkm_report_cli import report_cli
from gkm_three_point_descendants import read_report


KIND = "gkm_localization.bl2_double_exceptional_singletons"
NAMESPACE = "BlowupTwoDoubleExceptionalSingletons"
MARKINGS = (("unit", 4), ("H", 3), ("E1", 3), ("E2", 3), ("pt", 2))
REQUESTS = {"X0": [], "X1": [],
            "X2": [(beta, (power,), (label,)) for beta in ((2, 0, 0), (0, 2, 0))
                   for label, power in MARKINGS]}


def emit(raw):
    _, grouped = read_report(raw, requests=REQUESTS, genus=2, kind=KIND)
    incoming = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
                for c in grouped["X2"]}
    source = ordered_surface_frame(raw, [incoming[q] for q in REQUESTS["X2"]],
                                   lean_target=".blowupTwo", namespace=NAMESPACE,
                                   title="All genus-two singletons on the two doubled exceptional curves",
                                   generator="gkm_bl2_double_exceptional_singletons.py")
    source = source.replace("public import AxiomaticGW.Surfaces.Queries",
                            "public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalSingletons")
    source = source.replace("] : Array (SurfaceQuery", "] :\n    Array (SurfaceQuery")
    end = f"end AxiomaticGW.GKM.{NAMESPACE}\n"
    return source.removesuffix(end) + '''open SurfaceGenusTwoBlowupDescendants

/-- The fixed basis order on each exceptional axis is unit, hyperplane, E₁, E₂, point. -/
def index (axis : Fin 2) (basis : Fin 5) : Fin 10 :=
  ⟨5 * axis.val + basis.val, by omega⟩

private theorem covers (j : Fin 10) : ∃ axis basis, index axis basis = j := by
  revert j
  decide +kernel

/-- The native coordinate, label, power and ordinary value agree with the original query. -/
theorem binding (axis : Fin 2) (basis : Fin 5) :
    (requests (index axis basis), values (index axis basis)) =
      (AxiomaticGW.BlowupTwoDoubleExceptionalSingletons.request axis
        (BlowupTwoExceptionalOneMarking.labels basis),
       AxiomaticGW.BlowupTwoDoubleExceptionalSingletons.value axis
        (BlowupTwoExceptionalOneMarking.labels basis)) := by
  revert axis basis
  decide +kernel

/-- Every native ordinary singleton is checked by the original descendant reconstruction. -/
theorem accepted (j : Fin 10) : CheckedDescendant 0 (requests j) (values j) := by
  obtain ⟨axis, basis, rfl⟩ := covers j
  exact (congrArg (fun p ↦ CheckedDescendant 0 p.1 p.2) (binding axis basis)).mpr
    (AxiomaticGW.BlowupTwoDoubleExceptionalSingletons.checked axis
      (BlowupTwoExceptionalOneMarking.labels basis))

/-- The same reported row certifies reconstruction, full-field equality and specialization. -/
theorem certified (j : Fin 10) : CheckedDescendant 0 (requests j) (values j) ∧
    equivariant j = (values j : Coefficient) ∧ Specializes (equivariant j) (values j) :=
  ⟨accepted j, equivariant_eq_ordinary j, specializes j⟩

''' + end


if __name__ == "__main__":
    report_cli(__doc__, requests=REQUESTS, genus=2, kind=KIND, emit=emit)
