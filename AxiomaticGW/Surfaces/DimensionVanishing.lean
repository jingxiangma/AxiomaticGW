/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Queries

/-! # An ordinary GW vanishing certificate from the surface virtual dimension

A homogeneous descendant of the wrong total codimension has value zero. The
geometric-domain hypothesis retains positive-degree unstable arities and excludes
auxiliary degree-zero unstable conventions.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceQuery
variable {X : SurfaceTarget}

/-- Return a zero only when the signed virtual dimension and total codimension differ. -/
def dimensionVanishing? (q : SurfaceQuery X) : Option ℚ :=
  if q.DimensionCompatible then none else some 0

/-- A surface grading identification suffices to interpret every returned zero. -/
theorem dimensionVanishing?_sound {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
    (q : SurfaceQuery X) (hg : q.GeometricDomain) {v : ℚ} (hv : q.dimensionVanishing? = some v) :
    q.checkedEval U = some v := by
  by_cases hd : q.DimensionCompatible
  · simp only [dimensionVanishing?, if_pos hd, reduceCtorEq] at hv
  · simp only [dimensionVanishing?, if_neg hd, Option.some.injEq] at hv
    rw [checkedEval_of_geometricDomain U q hg, eval_eq_zero_of_dimension_incompatible U T q hd, hv]

end AxiomaticGW.SurfaceQuery
