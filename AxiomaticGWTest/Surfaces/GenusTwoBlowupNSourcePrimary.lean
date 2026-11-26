/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNSourcePrimary

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoBlowupNSourcePrimary
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupNRelation
open SurfaceGenusTwoBlowupNSourcePrimary

/-- The full shifted equation has no source-primary column, with arbitrary marking count. -/
public theorem combined_source_primary_zero (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (m : ℕ) :
    RationalTerms.coefficient (row X i beta)
      {Sum.inr (SurfaceQuery.points X 2 (beta + X.exceptionalCurve i) m)} = 0 :=
  row_source_primary_eq_zero i beta m

/-- Distinct exceptional divisors are allowed in the general source-class theorem. -/
public theorem cross_exceptional_triple (beta : SurfaceTarget.blowupTwo.Curve) (m n : ℕ) :
    RationalTerms.coefficient (bpRow .blowupTwo n beta
      ![.exceptional 0, .exceptional 1, .hyperplane])
      {Sum.inr (SurfaceQuery.points .blowupTwo 2 beta m)} = 0 := by
  apply normalized_primary_divisors_at_class
  intro t
  fin_cases t <;> rfl

/-- Class zero and zero added markings require no positive-energy assumption. -/
public theorem degree_zero_exceptional_triple (m : ℕ) :
    RationalTerms.coefficient (bpRow .hirzebruchOne 0 0
      ![.exceptional 0, .exceptional 0, .exceptional 0])
      {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 0 m)} = 0 := by
  apply normalized_primary_divisors_at_class
  intro t
  fin_cases t <;> rfl

/-- The vanishing concerns the same full class, even when its signed multiplicity is negative. -/
public theorem negative_multiplicity_source (m n : ℕ) :
    RationalTerms.coefficient (bpRow .hirzebruchOne n ![3, 1]
      ![.exceptional 0, .hyperplane, .hyperplane])
      {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![3, 1] m)} = 0 := by
  apply normalized_primary_divisors_at_class
  intro t
  fin_cases t <;> rfl

end AxiomaticGWTest.Surfaces.GenusTwoBlowupNSourcePrimary
