/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupLowPsi

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupLowPsi
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupLowPsi

/-- The descendant table comparison keeps the exact full class and every sector. -/
theorem direct_table_congr (X : SurfaceTarget) (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) (hk : q.totalPsi ≤ 1) (v w : State X → ℚ)
    (h : ∀ f, v (q.beta, f) = w (q.beta, f)) :
    descendantValueWith v q = descendantValueWith w q :=
  descendantValueWith_congr v w q hg hk h

/-- Ancestor comparison keeps every effective full-class tail, including exceptional classes. -/
theorem full_table_congr (X : SurfaceTarget) (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) (hk : q.totalPsi ≤ 1) (v w : State X → ℚ)
    (h : ∀ beta, (∃ delta, beta + delta = q.beta) → ∀ f, v (beta, f) = w (beta, f)) :
    ancestorValueWith v q = ancestorValueWith w q :=
  ancestorValueWith_congr v w q hg hk h

/-- A first exceptional power with two primary points at the reducible class 2E. -/
def doubleExceptional : SurfaceAncestorKey .hirzebruchOne :=
  SurfaceAncestorKey.ofLabels 2 (Fin 3) (by unfold StableArity; decide +kernel) ![2, 0]
    ![1, 0, 0] ![.exceptional 0, .point, .point]

/-- An artificial test table isolates the smaller E-class primary coefficient.
This is not a GW value or an additional numerical seed. -/
def exceptionalPrimaryTable : State .hirzebruchOne → ℚ :=
  fun s ↦ match s.2 with
    | .primary => if s.1 = ![1, 0] then 1 else 0
    | _ => 0

/-- The direct descendant evaluator does not consult the smaller exceptional primary class. -/
theorem direct_tail_absent : descendantValueWith exceptionalPrimaryTable doubleExceptional = 0 := by
  decide +kernel

/-- The ancestor evaluator retains the actual signed exceptional calibration tail. -/
theorem full_tail_retained : ancestorValueWith exceptionalPrimaryTable doubleExceptional = -1 := by
  decide +kernel

/-- The two evaluations differ on a blowup, so the plane tail-cancellation rule cannot be used. -/
theorem descendant_ancestor_difference :
    descendantValueWith exceptionalPrimaryTable doubleExceptional ≠
      ancestorValueWith exceptionalPrimaryTable doubleExceptional := by
  rw [direct_tail_absent, full_tail_retained]
  norm_num

/-- The occurrence adapter preserves the total power of the supplied ordered query. -/
theorem query_adapter_power (X : SurfaceTarget) (q : SurfaceQuery X) (hg : q.genus = 2) :
    (queryKey q hg).totalPsi = ∑ j : Fin q.insertions.length, (q.insertions.get j).psi := by
  exact SurfaceAncestorKey.totalPsi_ofLabels _ _ _ _ _ _

/-- Primary equality is justified by zero total power, rather than plane-only tail cancellation. -/
theorem primary_values_agree (X : SurfaceTarget) (values : State X → ℚ)
    (q : SurfaceAncestorKey X) (hp : q.IsPrimary) :
    ancestorValueWith values q = descendantValueWith values q :=
  ancestorValueWith_eq_descendantValueWith_of_primary values q hp

section Interpretation
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Canonical descendant values at the exact full class interpret the direct polynomial. -/
theorem direct_table_interpretation (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (values : State X → ℚ) (q : SurfaceAncestorKey X) (hg : q.genus = 2)
    (hk : q.totalPsi ≤ 1)
    (hv : ∀ f : Family X, values (q.beta, f) = (f.query q.beta).eval U) :
    descendantValueWith values q =
      RationalTerms.eval (variableEval U P) (directNormalizedTerms q) :=
  descendantValueWith_eval U P values q hg hk hv

/-- Ancestor interpretation requires full subclass values and preserves their corrections. -/
theorem full_table_interpretation (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (values : State X → ℚ) (q : SurfaceAncestorKey X) (hg : q.genus = 2)
    (hk : q.totalPsi ≤ 1)
    (hv : ∀ beta : X.Curve, (∃ delta : X.Curve, beta + delta = q.beta) →
      ∀ f : Family X, values (beta, f) = (f.query beta).eval U) :
    ancestorValueWith values q =
      RationalTerms.eval (variableEval U P) (normalizedTerms q) :=
  ancestorValueWith_eval U P values q hg hk hv

end Interpretation

end AxiomaticGWTest.SurfaceGenusTwoBlowupLowPsi
