/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHSupport

/-!
# Subcritical H-support consumers

The exact source-class vanishing is tested in the normalized row at arbitrary
full classes, mixed negative signed multiplicities and both exceptional shifts.
Zero remainder, nonzero exceptional remainder, the critical point budget and
energy zero retain their distinct applicability conditions.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupHSupport
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo SurfaceGenusTwoBlowupHPivots
  SurfaceGenusTwoBlowupHContributions SurfaceGenusTwoBlowupHSupport

/-- The source-class column is excluded without an added support premise. -/
theorem source_column_uniform (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient (row X i beta) {hColumn X (sourceCurve X i beta)} = 0 :=
  source_column_row_coefficient_eq_zero X i beta hbeta

/-- At zero remainder the arbitrary point count still belongs to the original equation. -/
theorem zero_remainder_arbitrary_budget (X : SurfaceTarget) (i : Fin X.blowups)
    (gamma : X.Curve) (n : ℕ) (hn : n < X.effective.energy gamma - 1) :
    L24Relation.pointCoefficient X n gamma (labels X i) (hColumn X gamma) = 0 := by
  have h := pointCoefficient_eq_zero_of_subcritical X i gamma 0 (map_zero _) n hn
  simpa only [add_zero] using h

/-- Every node state, including the selected point, vanishes below the physical budget. -/
theorem all_node_states_subcritical (X : SurfaceTarget) (gamma delta : X.Curve)
    (m : ℕ) (hm : m < X.effective.energy gamma - 1) (b : SurfaceBasisLabel X) :
    remainderVertex X (hColumn X gamma) (coefficientVertex X (hColumn X gamma)) m
      2 (Fin 2) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance delta
      ![.hyperplane, b] = 0 :=
  remainderVertex_hyperplane_pair_eq_zero_of_subcritical X gamma delta m hm b

/-- The F1 source remains a different full class even at negative signed multiplicity. -/
theorem hirzebruchOne_negative_source_column :
    RationalTerms.coefficient (row .hirzebruchOne 0 ![2, 1])
      {hColumn .hirzebruchOne ![3, 1]} = 0 := by
  have h := source_column_row_coefficient_eq_zero .hirzebruchOne 0 ![2, 1]
    (by decide +kernel)
  have hs : sourceCurve .hirzebruchOne 0 ![2, 1] = ![3, 1] := by decide +kernel
  rw [hs] at h
  exact h

/-- The mixed Bl2P2 target admits source-class exclusion at either exceptional shift. -/
theorem blowupTwo_mixed_both_source_columns (i : Fin 2) :
    RationalTerms.coefficient (row .blowupTwo i ![2, 3, 1])
      {hColumn .blowupTwo (sourceCurve .blowupTwo i ![2, 3, 1])} = 0 :=
  source_column_row_coefficient_eq_zero .blowupTwo i ![2, 3, 1] (by decide +kernel)

/-- A nonzero exceptional remainder is retained in the same full coefficient identity. -/
theorem nonzero_exceptional_remainder_subcritical :
    L24Relation.pointCoefficient .blowupTwo 0
      (![2, 3, 1] + SurfaceTarget.blowupTwo.exceptionalCurve 1)
      (labels .blowupTwo 0) (hColumn .blowupTwo ![2, 3, 1]) = 0 :=
  pointCoefficient_eq_zero_of_subcritical .blowupTwo 0 ![2, 3, 1]
    (SurfaceTarget.blowupTwo.exceptionalCurve 1)
    (SurfaceTarget.blowupTwo.planeDegree_exceptionalCurve 1) 0 (by decide +kernel)

/-- At the critical budget the diagonal coefficient is nonzero; the strict bound matters. -/
theorem critical_budget_is_distinct (X : SurfaceTarget) (i : Fin X.blowups)
    (gamma : X.Curve) (hgamma : 0 < X.effective.energy gamma) :
    ¬pointCount X gamma < X.effective.energy gamma - 1 ∧ coefficient X i gamma = -1 := by
  refine ⟨?_, coefficient_eq_neg_one X i gamma hgamma⟩
  unfold pointCount
  exact Nat.lt_irrefl _

/-- Natural subtraction at class zero supplies no subcritical point budget. -/
theorem class_zero_not_subcritical (X : SurfaceTarget) (n : ℕ) :
    ¬n < X.effective.energy (0 : X.Curve) - 1 := by
  rw [map_zero, Nat.zero_sub]
  exact Nat.not_lt_zero _

end AxiomaticGWTest.SurfaceGenusTwoBlowupHSupport
