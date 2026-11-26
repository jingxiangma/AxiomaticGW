/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupQuantumIdempotents

/-! # Nonzero first-order projector corrections for all five primitive blowup classes -/

@[expose] public section
namespace AxiomaticGWTest.GKM.BlowupQuantumIdempotents
open AxiomaticGW.GKM EquivariantCoefficients FirstOrderFixedPoints
open AxiomaticGW.GKM.BlowupQuantumIdempotents

/-- The exceptional curve and the fiber each move a classical F₁ projector. -/
theorem one_blowup_each_moves (d : Fin 2) :
    ∃ i : Fin 4, coeff (projector SurfaceFrames.OneBlowup.request.euler
      OneBlowup.pairs OneBlowup.weights i) d i ≠ 0 := by
  fin_cases d
  · refine ⟨1, ?_⟩
    rw [projector_coefficient]
    simp +decide [changeOfBasis, Pair.diff, OneBlowup.pairs, OneBlowup.weights,
      SurfaceFrames.OneBlowup.request, Fin.sum_univ_three, Matrix.cons_val_two,
      y_ne_zero, x_sub_y_ne_zero]
  · refine ⟨0, ?_⟩
    rw [projector_coefficient]
    simp +decide [changeOfBasis, Pair.diff, OneBlowup.pairs, OneBlowup.weights,
      SurfaceFrames.OneBlowup.request, Fin.sum_univ_three, Matrix.cons_val_two,
      y_ne_zero, x_sub_y_ne_zero]

/-- The equal-energy curves E₁,E₂,L each move an explicitly supported Bl₂ projector. -/
theorem two_blowups_each_moves (d : Fin 3) :
    ∃ i : Fin 5, coeff (projector SurfaceFrames.TwoBlowups.request.euler
      TwoBlowups.pairs TwoBlowups.weights i) d i ≠ 0 := by
  fin_cases d
  · refine ⟨1, ?_⟩
    rw [projector_coefficient]
    simp +decide [changeOfBasis, Pair.diff, TwoBlowups.pairs, TwoBlowups.weights,
      SurfaceFrames.TwoBlowups.request, Fin.sum_univ_three, Matrix.cons_val_two,
      y_ne_zero, x_sub_y_ne_zero]
  · refine ⟨3, ?_⟩
    rw [projector_coefficient]
    simp +decide [changeOfBasis, Pair.diff, TwoBlowups.pairs, TwoBlowups.weights,
      SurfaceFrames.TwoBlowups.request, Fin.sum_univ_three, Matrix.cons_val_two,
      Matrix.cons_val_three, x_ne_zero, y_ne_zero]
  · refine ⟨2, ?_⟩
    rw [projector_coefficient]
    simp +decide [changeOfBasis, Pair.diff, TwoBlowups.pairs, TwoBlowups.weights,
      SurfaceFrames.TwoBlowups.request, Fin.sum_univ_three, Matrix.cons_val_two,
      x_ne_zero, y_sub_x_ne_zero]

end AxiomaticGWTest.GKM.BlowupQuantumIdempotents
