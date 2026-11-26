/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.Queries

/-! # Fixed query and seed regressions

The tests distinguish geometric queries from degree-zero auxiliary values,
check the signed virtual dimension and finite seed counts, and exercise the
connection to the supplied numerical invariant.
-/

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces

open AxiomaticGW

example : Fintype.card (SurfaceSeed .plane) = 4 := by decide
example : Fintype.card (SurfaceSeed .hirzebruchOne) = 7 := by decide
example : Fintype.card (SurfaceSeed .blowupTwo) = 10 := by decide

/-- Seed classes have the intended full lattice coordinates, not just the
correct anticanonical energy. -/
example : SurfaceTarget.hirzebruchOne.latticeCoordinates
    SurfaceTarget.hirzebruchOne.lineCurve = ![1, 0] := by decide
example : SurfaceTarget.blowupTwo.latticeCoordinates
    SurfaceTarget.blowupTwo.lineCurve = ![1, 0, 0] := by decide
example : SurfaceTarget.blowupTwo.latticeCoordinates
    (SurfaceTarget.blowupTwo.exceptionalCurve 1) = ![0, 0, 1] := by decide

/-- The two-point line seed is geometric although its underlying curve arity is unstable. -/
example : (SurfaceSeed.line (X := .plane)).query.GeometricDomain ∧
    ¬StableArity 0 (Fin 2) := by
  constructor
  · decide
  · norm_num [StableArity]

/-- The exceptional seed has no markings and is still a geometric query. -/
example : (SurfaceSeed.exceptional (X := .hirzebruchOne) 0).query.GeometricDomain ∧
    (SurfaceSeed.exceptional (X := .hirzebruchOne) 0).query.DimensionCompatible := by decide

/-- Degree-zero unstable values are excluded, and virtual dimension minus
one must not be truncated to zero. -/
example : ¬(SurfaceQuery.mk (X := .plane) 0 0 []).GeometricDomain ∧
    ¬(SurfaceQuery.mk (X := .plane) 0 0 []).DimensionCompatible := by decide

/-- Distinct exceptional classes remain distinct even though their energies agree. -/
example : (SurfaceSeed.exceptional (X := .blowupTwo) 0).query ≠
    (SurfaceSeed.exceptional (X := .blowupTwo) 1).query := by decide

example : (SurfaceSeed.genusOneUnit (X := .plane)).value = 1 / 8 :=
  SurfaceTarget.genusOneDilaton_plane
example : (SurfaceSeed.genusOneUnit (X := .hirzebruchOne)).value = 1 / 6 :=
  SurfaceTarget.genusOneDilaton_hirzebruchOne
example : (SurfaceSeed.genusOneUnit (X := .blowupTwo)).value = 5 / 24 :=
  SurfaceTarget.genusOneDilaton_blowupTwo
example : (SurfaceSeed.genusOneExceptional (X := .hirzebruchOne) 0).value = -1 / 24 := rfl
example : (SurfaceSeed.genusTwoExceptional (X := .blowupTwo) 1).value = -1 / 2880 := rfl

/-- The first positive primary plane genus-two benchmark has thirteen point
insertions in degree four. This tests its shape, not its numerical value. -/
example : (SurfaceQuery.mk (X := .plane) 2 (fun _ ↦ 4)
    (List.replicate 13 ⟨.point, 0⟩)).DimensionCompatible := by decide

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- The finite hypothesis supplies an equality of the existing invariant,
rather than an equality for an unrelated seed lookup function. -/
example (U : UnstableDescendantConventions M I) (h : SurfaceSeed.SeedValues U) :
    (SurfaceSeed.line (X := X)).query.eval U = 1 := h .line

example (U : UnstableDescendantConventions M I) :
    (SurfaceQuery.mk (X := X) 0 0 []).checkedEval U = none := by
  apply SurfaceQuery.checkedEval_of_not_geometricDomain
  norm_num [SurfaceQuery.GeometricDomain, StableArity]

example (U : UnstableDescendantConventions M I) (h : SurfaceSeed.SeedValues U) :
    (SurfaceSeed.line (X := X)).query.checkedEval U = some 1 := by
  rw [SurfaceQuery.checkedEval_of_geometricDomain U _
    (SurfaceSeed.query_geometricDomain .line), h .line]
  rfl

example (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (q : SurfaceQuery X)
    (h : ¬q.DimensionCompatible) : q.eval U = 0 :=
  q.eval_eq_zero_of_dimension_incompatible U T h

end AxiomaticGWTest.Surfaces
