/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupBoundary

/-!
# Boundary consumers on F1 and Bl2P2

The finite tables, full reducible exceptional classes, nominal P0 dimension
rejection and the positive energy-one P query are checked separately.
The final consumer uses the original unsolved equation, with no N0 seed.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupBoundary
open AxiomaticGW SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupBoundary

/-- All four F1 class-zero entries use the stated finite constants and derived zeros. -/
theorem hirzebruchOne_zero_values :
    value (X := .hirzebruchOne) 0 .hyperplane = -1 / 960 ∧
      value (X := .hirzebruchOne) 0 .point = 0 ∧
      value (X := .hirzebruchOne) 0 .primary = 0 ∧
      value (X := .hirzebruchOne) 0 (.exceptional 0) = -1 / 2880 := by
  decide +kernel

/-- Bl2P2 retains each exceptional label in its class-zero table. -/
theorem blowupTwo_zero_values :
    value (X := .blowupTwo) 0 .hyperplane = -1 / 960 ∧
      value (X := .blowupTwo) 0 .point = 0 ∧
      value (X := .blowupTwo) 0 .primary = 0 ∧
      value (X := .blowupTwo) 0 (.exceptional 0) = -1 / 2880 ∧
      value (X := .blowupTwo) 0 (.exceptional 1) = -1 / 2880 := by
  decide +kernel

/-- Mixed reducible pure exceptional classes keep both full effective coordinates. -/
theorem blowupTwo_mixed_exceptional_value (family : Family .blowupTwo) :
    value ![2, 3, 0] family = 0 :=
  value_of_ne_zero _ (by decide +kernel) family

/-- Repeated exceptional classes are covered without an irreducibility restriction. -/
theorem hirzebruchOne_repeated_exceptional_value (family : Family .hirzebruchOne) :
    value ![3, 0] family = 0 :=
  value_of_ne_zero _ (by decide +kernel) family

/-- Natural subtraction does not turn the nominal class-zero P state into a valid dimension. -/
theorem point_zero_dimension_rejected (X : SurfaceTarget) :
    ¬ (Family.point.query (0 : X.Curve)).DimensionCompatible :=
  point_zero_not_dimensionCompatible X

/-- At energy one, the P query is dimension-compatible despite having no extra point. -/
theorem exceptional_generator_point_dimension (X : SurfaceTarget) (i : Fin X.blowups) :
    (Family.point.query (X.exceptionalCurve i)).DimensionCompatible := by
  rw [Family.query, SurfaceGenusTwo.point_first_dimensionCompatible_iff]
  exact X.exceptionalCurve_ne_zero i

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- The energy-one point query vanishes by its own point marking and named support. -/
theorem exceptional_generator_point_boundary (i : Fin X.blowups)
    (U : UnstableDescendantConventions M I)
    (V : StableMapIntersection U) (hV : ExceptionalPointSupport V) :
    value (X.exceptionalCurve i) .point = (Family.point.query (X.exceptionalCurve i)).eval U := by
  rw [value_of_ne_zero _ (X.exceptionalCurve_ne_zero i)]
  have hd : X.divisorIntersections (X.exceptionalCurve i) 0 = 0 :=
    (X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero _).mp
      (X.planeDegree_exceptionalCurve i)
  exact (SurfaceGenusTwo.exceptional_first_point_eval_eq_zero V hV _
    (X.exceptionalCurve_ne_zero i) hd).symm

/-- The public state interface derives the whole boundary from the original equation.
Only the finite H/K seed values and class-level geometric support are supplied. -/
theorem original_equation_state_boundary (i : Fin X.blowups)
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega)
    (V : StableMapIntersection U) (hV : ExceptionalPointSupport V)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
    (hEtwo : ∀ j, (SurfaceSeed.genusTwoExceptional j : SurfaceSeed X).query.eval U =
      -1 / 2880)
    (heq : InitialEquation X (SurfacePolynomialReduction.variableEval U P))
    (s : State X) (hd : X.planeDegree s.1 = 0) :
    value s.1 s.2 = (s.2.query s.1).eval U :=
  value_eq_eval_of_initialEquation i U P T V hV hHtwo hEtwo heq s.1 hd s.2

end AxiomaticGWTest.SurfaceGenusTwoBlowupBoundary
