/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupOrder
public import AxiomaticGW.Surfaces.GenusTwoExceptionalInitialValues

/-!
# The plane-degree-zero boundary for the blowup reconstruction

The executable table retains each full effective class and exceptional label.
It is zero on nonzero classes and has class-zero entries `H=-1/960`,
`K_i=-1/2880`, `N=0` and `P=0`. Soundness is asserted only at plane degree zero.
The nominal `P_0` query is zero by dimension, not an additional finite seed.

The first soundness lemma explicitly takes an intermediate derived `N_0` value.
The second discharges it from the original normalized BP initial equation,
finite divisor seeds and named exceptional evaluation support. F1 uses its
exceptional BP equation. On Bl2P2 the original line equation already determines
`N_0`. The cross-exceptional deduction remains in the existing initial-values
module. Neither an assumed solved recurrence nor an independent primary seed
is introduced here.

Primitive geometry producing the original equations and the class-level point
support remains separate. This module does not construct those geometric inputs
or prove complete reconstruction.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupBoundary
open SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction

variable {X : SurfaceTarget}

/-- The finite class-zero table uses only divisor seeds and derived zeros. -/
def initial : Family X → ℚ
  | .hyperplane => -1 / 960
  | .point => 0
  | .primary => 0
  | .exceptional _ => -1 / 2880

/-- Total executable boundary table, retaining the full effective class.
Its agreement with GW evaluation is proved only in the plane-degree-zero sector. -/
def value (beta : X.Curve) (family : Family X) : ℚ :=
  if beta = 0 then initial family else 0

/-- Class zero returns the finite table without a positivity assumption. -/
theorem value_zero (family : Family X) : value (0 : X.Curve) family = initial family :=
  if_pos rfl

/-- Every nonzero full class receives zero in the total boundary table. -/
theorem value_of_ne_zero (beta : X.Curve) (hb : beta ≠ 0) (family : Family X) :
    value beta family = 0 := if_neg hb

/-- The nominal point-descendant state at class zero is dimension-incompatible. -/
theorem point_zero_not_dimensionCompatible (X : SurfaceTarget) :
    ¬ (Family.point.query (0 : X.Curve)).DimensionCompatible := by
  rw [Family.query, SurfaceGenusTwo.point_first_dimensionCompatible_iff]
  exact not_not.mpr rfl

variable {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Dimension vanishing supplies the nominal zero-class P value. -/
theorem point_zero_eval_eq_zero (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) :
    (Family.point.query (0 : X.Curve)).eval U = 0 :=
  SurfaceQuery.eval_eq_zero_of_dimension_incompatible U T _
    (point_zero_not_dimensionCompatible X)

/-- Intermediate boundary soundness with `N_0` explicitly distinguished from a seed.
The original-equation theorem below discharges this derived-value premise. -/
theorem value_eq_eval_of_zero_primary (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega)
    (V : StableMapIntersection U) (hV : ExceptionalPointSupport V)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
    (hEtwo : ∀ i, (SurfaceSeed.genusTwoExceptional i : SurfaceSeed X).query.eval U =
      -1 / 2880)
    (hNzero : (SurfaceQuery.points X 2 0 1).eval U = 0)
    (beta : X.Curve) (hd : X.planeDegree beta = 0) (family : Family X) :
    value beta family = (family.query beta).eval U := by
  by_cases hb : beta = 0
  · subst beta
    rw [value_zero]
    cases family with
    | hyperplane =>
      change (-1 / 960 : ℚ) =
        (SurfaceFirstDescendant.query 2 0 .hyperplane (X.effective.energy 0)).eval U
      rw [map_zero]
      exact hHtwo.symm
    | point => exact (point_zero_eval_eq_zero U T).symm
    | primary =>
      change (0 : ℚ) =
        (SurfaceQuery.points X 2 0 (X.effective.energy 0 + 1)).eval U
      rw [map_zero]
      exact hNzero.symm
    | exceptional i =>
      change (-1 / 2880 : ℚ) =
        (SurfaceFirstDescendant.query 2 0 (.exceptional i) (X.effective.energy 0)).eval U
      rw [map_zero]
      exact (hEtwo i).symm
  · rw [value_of_ne_zero beta hb]
    have hi : X.divisorIntersections beta 0 = 0 :=
      (X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero beta).mp hd
    have he : 0 < X.effective.energy beta := Nat.pos_of_ne_zero
      (fun hz ↦ hb ((X.effective.energy_eq_zero_iff beta).mp hz))
    exact (SurfaceGenusTwo.exceptional_canonical_eval_eq_zero V hV beta hb hi
      (family.query beta) (family.query_mem_canonicalQueries beta (fun _ ↦ he))).symm

/-- The original unsolved normalized BP equation needed to derive `N_0`.
The plane branch is unused whenever an exceptional label has been supplied. -/
def InitialEquation : (X : SurfaceTarget) → (Variable X → ℚ) → Prop
  | .plane, _ => True
  | .hirzebruchOne, v =>
      RationalTerms.eval v (BelorousskiPandharipande.normalizedGenusTwoTerms
        .hirzebruchOne 0 ![1, 0] 0 (fun _ ↦ .exceptional 0)) = 0
  | .blowupTwo, v =>
      RationalTerms.eval v (BelorousskiPandharipande.normalizedGenusTwoTerms
        .blowupTwo 0 ![0, 0, 1] 0 ![.exceptional 0, .exceptional 1, .hyperplane]) = 0

/-- Bl2P2's original line equation and finite divisor seeds determine `N_0`.
The complete polynomial is used, including its lower-genus constant. -/
theorem blowupTwo_zero_primary_of_equation
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.blowupTwo.blowups)
      SurfaceTarget.blowupTwo.Curve SurfaceTarget.blowupTwo.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed .blowupTwo).query.eval U =
      -1 / 960)
    (hEtwo : ∀ i, (SurfaceSeed.genusTwoExceptional i : SurfaceSeed .blowupTwo).query.eval U =
      -1 / 2880)
    (heq : InitialEquation .blowupTwo (variableEval U P)) :
    (SurfaceQuery.points .blowupTwo 2 0 1).eval U = 0 := by
  change RationalTerms.eval (variableEval U P)
    (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 0 ![0, 0, 1] 0
      ![.exceptional 0, .exceptional 1, .hyperplane]) = 0 at heq
  rw [SurfaceGenusTwoNormalizedBP.eval_blowupTwoLine] at heq
  simp only [SurfaceGenusTwoNormalizedBP.blowupTwoLine, RationalTerms.eval_add,
    RationalTerms.eval_term, Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply, mul_one, variableEval] at heq
  have hH : (SurfaceFirstDescendant.query 2 (0 : SurfaceTarget.blowupTwo.Curve)
      .hyperplane 0).eval U = -1 / 960 := hHtwo
  have hE (i : Fin SurfaceTarget.blowupTwo.blowups) :
      (SurfaceFirstDescendant.query 2 (0 : SurfaceTarget.blowupTwo.Curve)
        (.exceptional i) 0).eval U = -1 / 2880 := hEtwo i
  rw [hH, hE, hE] at heq
  linarith

/-- An actual exceptional label restricts the target to F1 or Bl2P2. The original
unsolved BP initial equation derives `N_0` from the finite divisor seeds and support. -/
theorem zero_primary_of_initialEquation (i : Fin X.blowups)
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (V : StableMapIntersection U) (hV : ExceptionalPointSupport V)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
    (hEtwo : ∀ j, (SurfaceSeed.genusTwoExceptional j : SurfaceSeed X).query.eval U =
      -1 / 2880)
    (heq : InitialEquation X (variableEval U P)) :
    (SurfaceQuery.points X 2 0 1).eval U = 0 := by
  cases X with
  | plane => exact i.elim0
  | hirzebruchOne =>
      exact SurfaceGenusTwo.hirzebruchOne_zero_primary_of_equation
        U P V hV (hEtwo 0) heq
  | blowupTwo => exact blowupTwo_zero_primary_of_equation U P hHtwo hEtwo heq

/-- Boundary soundness from the original unsolved equation, finite divisor seeds,
dimension vanishing and named point-evaluation support. No independent `N_0` seed remains. -/
theorem value_eq_eval_of_initialEquation (i : Fin X.blowups)
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega)
    (V : StableMapIntersection U) (hV : ExceptionalPointSupport V)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
    (hEtwo : ∀ j, (SurfaceSeed.genusTwoExceptional j : SurfaceSeed X).query.eval U =
      -1 / 2880)
    (heq : InitialEquation X (variableEval U P))
    (beta : X.Curve) (hd : X.planeDegree beta = 0) (family : Family X) :
    value beta family = (family.query beta).eval U :=
  value_eq_eval_of_zero_primary U T V hV hHtwo hEtwo
    (zero_primary_of_initialEquation i U P V hV hHtwo hEtwo heq) beta hd family

end AxiomaticGW.SurfaceGenusTwoBlowupBoundary
