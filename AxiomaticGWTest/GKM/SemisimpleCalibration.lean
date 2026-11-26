/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PrimitiveLoopTranslation

/-! # Exact nonzero transition coefficients and a node/retained-marking sign check -/

@[expose] public section
namespace AxiomaticGWTest.GKM.SemisimpleCalibration
open AxiomaticGW.GKM EquivariantCoefficients FirstOrderFixedPoints EquivariantCalibrationReplay
open AxiomaticGW.GKM.SemisimpleCalibration

/-- Swapping the zero-power node and the one-psi marking reverses this plane coefficient. -/
theorem plane_psi_sign : paired .plane 1 0 1 2 = 1 ∧ paired .plane 1 0 2 1 = -1 := by
  constructor <;> rfl

/-- The plane (0,1) primary inverse-loop coefficient is a nonzero character fraction. -/
theorem plane_transition : fixedOperator .plane 0 0 0 1 = -1 / (y*(x-y)) := by
  apply mul_left_cancel₀ (show (3 : Coefficient) ≠ 0 by norm_num)
  calc
    3 * fixedOperator .plane 0 0 0 1 = _ := primary_gap .plane 0 0 1 (by decide)
    _ = _ := by
      simp +decide [request, SurfaceFrames.Plane.request, presentation,
        PlaneQuantumPairs.presentation,
        changeOfBasis, PlaneQuantumPairs.pairs, PlaneQuantumPairs.weights, Pair.diff,
        Fin.sum_univ_three, Matrix.cons_val_two]
      field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero]
      ring

/-- The equal-energy E₁ and E₂ classes have different primary transitions at the same pair. -/
theorem two_blowups_transitions :
    fixedOperator .blowupTwo 0 0 1 2 = -y/(x-y) ∧ fixedOperator .blowupTwo 0 1 1 2 = 0 := by
  have h (d : Fin 3) : fixedOperator .blowupTwo 0 d 1 2 =
      ((request .blowupTwo).tangentSum 1 - (request .blowupTwo).tangentSum 2) *
        changeOfBasis (request .blowupTwo).euler (presentation .blowupTwo).pairs
          (presentation .blowupTwo).weights d (Pi.single 2 1) 1 := by
    have he : energy .blowupTwo d = 1 := by fin_cases d <;> rfl
    simpa only [he, Nat.cast_one, one_mul] using primary_gap .blowupTwo d 1 2 (by decide)
  rw [h, h]
  simp +decide [request, presentation, BlowupQuantumIdempotents.TwoBlowups.presentation,
    changeOfBasis, BlowupQuantumIdempotents.TwoBlowups.pairs,
    BlowupQuantumIdempotents.TwoBlowups.weights, SurfaceFrames.TwoBlowups.request, Pair.diff,
    Fin.sum_univ_three, Matrix.cons_val_two]
  field_simp [x_sub_y_ne_zero]

private theorem plane_gap : gap .plane 0 0 1 = y := by
  change ((x + y) - (x - 2*y)) / (3 : Coefficient) = y
  ring

/-- The specified translation affects the diagonal only. The native plane coefficient at
positive loop power one is nonzero before ordinary specialization. -/
theorem plane_linear_loop (u : Fin 3 → Coefficient) :
    PrimitiveLoopTranslation.withTranslation .plane 0 u 0 1 = 1 / (y^3 * (x-y)) := by
  rw [((PrimitiveLoopTranslation.eq_iff .plane 0 u _).mp rfl).1 0 1 (by decide),
    plane_transition, plane_gap]
  field_simp [y_ne_zero, x_sub_y_ne_zero]

/-- Even at first Novikov degree the resolvent has a genuine quadratic Taylor term. -/
theorem plane_quadratic_taylor :
    CalibrationSpectrum.taylorCoefficient (fixedOperator .plane 0 0 0 1) (gap .plane 0 0 1) 2 =
      1 / (y^4 * (x-y)) ∧ (1 / (y^4 * (x-y)) : Coefficient) ≠ 0 := by
  rw [plane_transition, plane_gap]
  constructor
  · unfold CalibrationSpectrum.taylorCoefficient
    field_simp [y_ne_zero, x_sub_y_ne_zero]
  · exact one_div_ne_zero (mul_ne_zero (pow_ne_zero _ y_ne_zero) x_sub_y_ne_zero)

/-- The same off-diagonal component retains the full exceptional curve class. -/
theorem two_blowups_linear_loop (u : Fin 5 → Coefficient) :
    PrimitiveLoopTranslation.withTranslation .blowupTwo 0 u 1 2 = y / (x-y)^3 ∧
    PrimitiveLoopTranslation.withTranslation .blowupTwo 1 u 1 2 = 0 := by
  have hgap : gap .blowupTwo 0 1 2 = x-y := by
    have he : energy .blowupTwo 0 = 1 := rfl
    rw [gap, he, Nat.cast_one, div_one]
    rfl
  rw [((PrimitiveLoopTranslation.eq_iff .blowupTwo 0 u _).mp rfl).1 1 2 (by decide),
    ((PrimitiveLoopTranslation.eq_iff .blowupTwo 1 u _).mp rfl).1 1 2 (by decide),
    two_blowups_transitions.1, two_blowups_transitions.2, neg_zero, zero_div, hgap]
  refine ⟨?_, rfl⟩
  field_simp [x_sub_y_ne_zero]

end AxiomaticGWTest.GKM.SemisimpleCalibration
