/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroExceptionalPoints

/-!
# Lower-layer exceptional point consumers

These tests preserve the exceptional generator and fiber seeds, cover arbitrary
pure and mixed exceptional multiplicities, and check the actual rational
point-pair tail at every node state, energy zero and energy one. They import
only the genus-zero module, so the lower-layer API does not rely on genus-two
order or normalization declarations.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusZeroExceptionalPoints
open AxiomaticGW SurfaceGenusZero

/-- Every full exceptional-supported class is retained, without an irreducibility premise. -/
theorem all_exceptional_supported_point_values (X : SurfaceTarget) (beta : X.Curve)
    (hd : X.divisorIntersections beta 0 = 0) (he : 2 ≤ X.effective.energy beta) :
    pointValue X beta = 0 :=
  pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two X beta hd he

/-- Arbitrary exceptional multiples on F1 vanish above the unchanged generator seed. -/
theorem hirzebruchOne_arbitrary_multiple (k : ℕ) (hk : 2 ≤ k) :
    pointValue .hirzebruchOne ![k, 0] = 0 := by
  apply pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two
  · rfl
  · change 2 ≤ ∑ i : Fin 2, SurfaceTarget.hirzebruchOne.weights i * (![k, 0] : Fin 2 → ℕ) i
    rw [Fin.sum_univ_two]
    simpa only [SurfaceTarget.weights, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul, mul_zero, add_zero] using hk

/-- Mixed exceptional sums on Bl2P2 keep both full coordinates independently. -/
theorem blowupTwo_arbitrary_mixed_multiplicity (k l : ℕ) (hkl : 2 ≤ k + l) :
    pointValue .blowupTwo ![k, l, 0] = 0 := by
  apply pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two
  · rfl
  · change 2 ≤ ∑ i : Fin 3, SurfaceTarget.blowupTwo.weights i * (![k, l, 0] : Fin 3 → ℕ) i
    rw [Fin.sum_univ_three]
    simp only [SurfaceTarget.weights, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, one_mul]
    change 2 ≤ k + l
    exact hkl

/-- The energy-one exceptional initial value remains one on every selected generator. -/
theorem exceptional_generator_seed_preserved (X : SurfaceTarget) (i : Fin X.blowups) :
    pointValue X (X.exceptionalCurve i) = 1 :=
  pointValue_exceptional_generator X i

/-- The actual cotangent-tail label type is Option Bool; no flag reindexing is needed. -/
theorem tail_all_full_classes_and_node_states (X : SurfaceTarget) (beta : X.Curve)
    (hd : X.divisorIntersections beta 0 = 0) (b : SurfaceBasisLabel X) (n : ℕ) :
    primaryScalar X (pointValue X) beta n (Option.elim · b (fun _ : Bool ↦ .point)) = 0 :=
  primaryScalar_point_point_tail_eq_zero X beta hd b n

/-- The classical class-zero tail vanishes for all added points and node states. -/
theorem tail_class_zero (X : SurfaceTarget) (b : SurfaceBasisLabel X) (n : ℕ) :
    primaryScalar X (pointValue X) 0 n (Option.elim · b (fun _ : Bool ↦ .point)) = 0 := by
  apply primaryScalar_point_point_tail_eq_zero
  cases X <;> rfl

/-- The point-pair tail vanishes even though its energy-one class has point value one. -/
theorem tail_at_generator_seed (X : SurfaceTarget) (i : Fin X.blowups)
    (b : SurfaceBasisLabel X) (n : ℕ) :
    pointValue X (X.exceptionalCurve i) = 1 ∧
      primaryScalar X (pointValue X) (X.exceptionalCurve i) n
        (Option.elim · b (fun _ : Bool ↦ .point)) = 0 := by
  refine ⟨pointValue_exceptional_generator X i, ?_⟩
  apply primaryScalar_point_point_tail_eq_zero
  cases X <;> fin_cases i <;> decide +kernel

/-- The equivalent three-flag vector convention remains available to rational graphs. -/
theorem node_point_point_vector (X : SurfaceTarget) (beta : X.Curve)
    (hd : X.divisorIntersections beta 0 = 0) (n : ℕ) (b : SurfaceBasisLabel X) :
    primaryScalar X (pointValue X) beta n ![b, .point, .point] = 0 :=
  primaryScalar_node_point_point_eq_zero X beta hd n b

/-- Energy at least two alone does not imply vanishing: the existing F1 fiber seed is one. -/
theorem fiber_seed_outside_exceptional_support :
    pointValue .hirzebruchOne ![0, 1] = 1 ∧
      SurfaceTarget.hirzebruchOne.divisorIntersections ![0, 1] 0 = 1 := by
  decide +kernel

end AxiomaticGWTest.SurfaceGenusZeroExceptionalPoints
