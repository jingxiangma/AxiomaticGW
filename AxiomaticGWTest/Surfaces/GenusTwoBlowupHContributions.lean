/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHContributions

/-!
# Consumers of the uniform shifted hyperplane pivot

These consumers exercise the full normalized equation at arbitrary effective
classes, negative signed multiplicities, reducible exceptional multiples, and
both exceptional generators. The positive-plane-degree cross-column examples
bind to the original normalized row, rather than a numerical graph diagnostic.
Class zero remains excluded by the explicit positive-energy hypothesis.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupHContributions
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo SurfaceGenusTwoBlowupHPivots
  SurfaceGenusTwoBlowupHContributions

/-- A downstream consumer needs no coefficient premise or invariant seed. -/
theorem full_normalized_row_uniform (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient (row X i beta) {hColumn X beta} = -1 :=
  row_coefficient_eq_neg_one X i beta hbeta

/-- A divisor node has zero coefficient even with the complete physical budget. -/
theorem hyperplane_node_zero (X : SurfaceTarget) (beta delta : X.Curve)
    (n : ℕ) (he : X.effective.energy beta = n + 1) :
    remainderVertex X (hColumn X beta) (coefficientVertex X (hColumn X beta)) n
      2 (Fin 2) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance delta
      ![.hyperplane, .hyperplane] = 0 := by
  rw [main_hyperplane_pair X beta delta n n le_rfl he .hyperplane,
    if_neg (by
      intro h
      have hp := h.2.1
      cases hp)]

/-- The selected point node preserves the full target class and all its points. -/
theorem point_node_one (X : SurfaceTarget) (beta : X.Curve)
    (n : ℕ) (he : X.effective.energy beta = n + 1) :
    remainderVertex X (hColumn X beta) (coefficientVertex X (hColumn X beta)) n
      2 (Fin 2) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0
      ![.hyperplane, .point] = 1 := by
  rw [main_hyperplane_pair X beta 0 n n le_rfl he .point, if_pos ⟨rfl, rfl, rfl⟩]

/-- F1 class H+E has a negative signed exceptional multiplicity. -/
theorem hirzebruchOne_negative_signed_multiplicity :
    SurfaceTarget.hirzebruchOne.signedMultiplicity ![2, 1] 0 = -1 ∧
      coefficient .hirzebruchOne 0 ![2, 1] = -1 := by
  exact ⟨by decide +kernel, coefficient_eq_neg_one .hirzebruchOne 0 ![2, 1]
    (by decide +kernel)⟩

/-- Reducible exceptional multiples belong to the same full effective monoid. -/
theorem hirzebruchOne_exceptional_multiple : coefficient .hirzebruchOne 0 ![3, 0] = -1 :=
  coefficient_eq_neg_one .hirzebruchOne 0 ![3, 0] (by decide +kernel)

/-- A mixed Bl2P2 class with both negative signed multiplicities admits both shifts. -/
theorem blowupTwo_mixed_both_generators (i : Fin 2) :
    coefficient .blowupTwo i ![2, 3, 1] = -1 :=
  coefficient_eq_neg_one .blowupTwo i ![2, 3, 1] (by decide +kernel)

/-- At source E1+E2+L, the E1-shifted row for E2+L has no E1+L H column.
The target and competing class have positive plane degree and equal energy. -/
theorem blowupTwo_positive_plane_cross_column :
    RationalTerms.coefficient (row .blowupTwo 0 ![0, 1, 1])
      {hColumn .blowupTwo ![1, 0, 1]} = 0 := by
  have h := pointCoefficient_at_exceptional_generator .blowupTwo 0 1 ![1, 0, 1]
    (by decide +kernel)
  rw [if_neg (by decide : (0 : Fin 2) ≠ 1)] at h
  rw [row, ← L24Relation.pointCoefficient_eq_full]
  rw [show sourceCurve .blowupTwo 0 ![0, 1, 1] =
      ![1, 0, 1] + SurfaceTarget.blowupTwo.exceptionalCurve 1 by decide +kernel,
    show pointCount .blowupTwo ![0, 1, 1] =
      pointCount .blowupTwo ![1, 0, 1] by decide +kernel]
  exact h

/-- The opposite exceptional coordinate retains the symmetric full-class distinction. -/
theorem blowupTwo_other_positive_plane_cross_column :
    RationalTerms.coefficient (row .blowupTwo 1 ![1, 0, 1])
      {hColumn .blowupTwo ![0, 1, 1]} = 0 := by
  have h := pointCoefficient_at_exceptional_generator .blowupTwo 1 0 ![0, 1, 1]
    (by decide +kernel)
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)] at h
  rw [row, ← L24Relation.pointCoefficient_eq_full]
  rw [show sourceCurve .blowupTwo 1 ![1, 0, 1] =
      ![0, 1, 1] + SurfaceTarget.blowupTwo.exceptionalCurve 0 by decide +kernel,
    show pointCount .blowupTwo ![1, 0, 1] =
      pointCount .blowupTwo ![0, 1, 1] by decide +kernel]
  exact h

/-- Natural subtraction at zero energy cannot justify this positive-energy theorem. -/
theorem class_zero_excluded (X : SurfaceTarget) :
    ¬0 < X.effective.energy (0 : X.Curve) := by
  rw [map_zero]
  exact Nat.not_lt_zero _

end AxiomaticGWTest.SurfaceGenusTwoBlowupHContributions
