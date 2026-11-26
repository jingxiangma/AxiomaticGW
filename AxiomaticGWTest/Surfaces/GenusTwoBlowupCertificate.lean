/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupCertificate

/-! Finite full-class replay rejects corrupt boundaries and missing or colliding dependencies. -/

@[expose] public section

namespace AxiomaticGWTest.Surfaces.GenusTwoBlowupCertificate
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
  SurfaceGenusTwoBlowupCertificate

-- These checks do not evaluate any positive-plane reconstructed value.
set_option maxRecDepth 20000

/-- Boundary data includes nominal P and reducible exceptional classes with signed multiplicity. -/
def boundaryStates : List (State .hirzebruchOne) :=
  [(0, .hyperplane), (0, .point), (0, .primary), (0, .exceptional 0),
    (![2, 0], .primary), (![3, 0], .exceptional 0)]

/-- Every listed boundary state is checked against the already derived initial values. -/
theorem boundary_table_accepted : checkCanonicalTable 0 boundaryStates
    (fun s ↦ SurfaceGenusTwoBlowupBoundary.value s.1 s.2) = true := by
  decide +kernel

/-- Changing the H seed to zero cannot pass even when all other candidate entries are zero. -/
theorem corrupt_boundary_rejected : checkCanonicalTable 0 boundaryStates (fun _ ↦ 0) = false := by
  decide +kernel

/-- The accepted literal boundary gives the original reconstructed class-zero H query. -/
theorem boundary_table_sound : SurfaceGenusTwoBlowupRecursion.values
    (X := .hirzebruchOne) 0 (0, .hyperplane) = -1 / 960 := by
  have h := checkCanonicalTable_sound 0 boundaryStates _ boundary_table_accepted
    (0, .hyperplane) (by simp only [boundaryStates, List.mem_cons]; tauto)
  simpa only [SurfaceGenusTwoBlowupBoundary.value_zero,
    SurfaceGenusTwoBlowupBoundary.initial] using h.symm

/-- Nominal class-zero P can be checked internally, but is rejected as a numerical claim. -/
theorem nominal_point_claim_rejected : checkCanonicalClaim 0 boundaryStates
    (fun s ↦ SurfaceGenusTwoBlowupBoundary.value s.1 s.2)
    ((Family.point : Family .hirzebruchOne).query 0) 0 = false := by
  decide +kernel

/-- A dimension-compatible held H claim binds its exact genus, class and insertions. -/
theorem boundary_h_claim_accepted : checkCanonicalClaim 0 boundaryStates
    (fun s ↦ SurfaceGenusTwoBlowupBoundary.value s.1 s.2)
    ((Family.hyperplane : Family .hirzebruchOne).query 0) (-1 / 960) = true := by
  decide +kernel

/-- An actual coefficient eighteen forces H_beta to occur in the complete collected P row. -/
theorem p_row_h_dependency (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve)
    (he : 0 < X.effective.energy beta) :
    (.inr (Family.hyperplane.query beta) : Variable X) ∈ rowVariables i (beta, .point) := by
  apply mem_rowVariables_of_coefficient_ne_zero
  have hc := SurfaceGenusTwoBlowupPCoefficients.hyperplane_coefficient beta he
  change RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row i (beta, .point))
    {Sum.inr (Family.hyperplane.query beta)} = 18 at hc
  rw [hc]
  norm_num

/-- Omitting all dependencies rejects every positive-plane P row,
independently of candidate data. -/
theorem missing_p_h_dependency_rejected (X : SurfaceTarget) (i : Fin X.blowups)
    (candidate : State X → ℚ) (beta : X.Curve) (hd : 0 < X.planeDegree beta)
    (he : 0 < X.effective.energy beta) :
    checkCanonicalRow i [] candidate (beta, .point) = false := by
  apply checkCanonicalRow_eq_false_of_missing i [] candidate (beta, .point) hd
    (.inr (Family.hyperplane.query beta)) (p_row_h_dependency X i beta he)
  · intro h
    have hf := congrArg Prod.snd (state_query_injective
      (a₁ := (beta, .hyperplane)) (a₂ := (beta, .point)) (Sum.inr.inj h))
    cases hf
  · intro t ht
    exact (List.not_mem_nil ht).elim

/-- Equal order measures still distinguish exceptional components of the stored full class. -/
theorem same_measure_class_collision_rejected :
    measure .blowupTwo (![1, 0, 1], .hyperplane) =
      measure .blowupTwo (![0, 1, 1], .hyperplane) ∧
    checkDependency [(![0, 1, 1], .hyperplane)] (![0, 0, 1], .primary)
      (.inr ((Family.hyperplane : Family .blowupTwo).query ![1, 0, 1])) = false := by
  constructor
  · decide +kernel
  · decide +kernel

/-- Abstract Earlier allows a larger-energy exact key. Actual row coefficients separately
obey the proved target-energy bound. -/
theorem exact_higher_energy_key_accepted : checkDependency
    [(![1, 1], .hyperplane)] (![0, 1], .primary)
    (.inr ((Family.hyperplane : Family .hirzebruchOne).query ![1, 1])) = true := by
  decide +kernel

/-- Two exceptional labels of identical curve and rank cannot substitute for one another. -/
theorem exceptional_label_collision_rejected : checkDependency
    [(![0, 0, 1], .exceptional 1)] (![0, 0, 2], .primary)
    (.inr ((Family.exceptional 0 : Family .blowupTwo).query ![0, 0, 1])) = false := by
  decide +kernel

/-- Accepted finite entries preserve the original evaluator even beyond the stored list. -/
theorem accepted_cache_preserves_every_state (X : SurfaceTarget) (i : Fin X.blowups)
    (states : List (State X)) (candidate : State X → ℚ)
    (hcheck : checkCanonicalTable i states candidate = true) :
    valuesCached i states candidate = SurfaceGenusTwoBlowupRecursion.values i :=
  valuesCached_eq i states candidate hcheck

/-- A held claim is tied to a stored exact full query, not a digest or reconstructed measure. -/
theorem accepted_claim_names_exact_query (X : SurfaceTarget) (i : Fin X.blowups)
    (states : List (State X)) (candidate : State X → ℚ) (q : SurfaceQuery X) (claimed : ℚ)
    (hcheck : checkCanonicalClaim i states candidate q claimed = true) :
    q.DimensionCompatible ∧ ∃ s ∈ states, q = s.2.query s.1 ∧
      SurfaceGenusTwoBlowupRecursion.values i s = claimed :=
  checkCanonicalClaim_sound i states candidate q claimed hcheck

end AxiomaticGWTest.Surfaces.GenusTwoBlowupCertificate
