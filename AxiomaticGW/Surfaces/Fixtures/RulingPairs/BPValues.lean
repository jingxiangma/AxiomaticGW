/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.BPSignedValues

/-! # Actual canonical dependencies of the unshifted ruling BP equations -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.BP
open SurfaceGenusTwoBlowupScalar BelorousskiPandharipande
open _root_.AxiomaticGW.BlowupTwoLineBP (canonicalFamily)

/-- The lower constant cancels against the actual initial divisor seeds. -/
theorem equation (i : Fin 2) (r : Fin 3) :
    ∑ b : Fin 5, fullCoefficients i r b * actual (curve i, canonicalFamily b) = 0 := by
  have h := reduced_row i (chartRow i r)
  change constant 0 (curve i, row (chartRow i r)) +
    ((∑ b : Fin 5, singletonCoefficient 0 (curve i, row (chartRow i r)) (variableAt i false b) *
       zeroValues b) + ∑ b, singletonCoefficient 0 (curve i, row (chartRow i r))
       (variableAt i true b) * actual (curve i, canonicalFamily b)) = 0 at h
  simp only [constant_value, full_coefficient] at h
  have seeds : (∑ b : Fin 5, singletonCoefficient 0 (curve i, row (chartRow i r))
      (variableAt i false b) * zeroValues b) = -constantValue r := by
    rw [Fin.sum_univ_five]
    rw [show (0 : Fin 5) = seedIndex 0 from rfl, show (3 : Fin 5) = seedIndex 1 from rfl,
      show (4 : Fin 5) = seedIndex 2 from rfl]
    simp only [seed_coefficient, show zeroValues 1 = 0 from rfl,
      show zeroValues 2 = 0 from rfl, mul_zero, add_zero]
    fin_cases i <;> fin_cases r <;> decide +kernel
  rw [seeds] at h
  linarith only [h]

/-- The point and foreign exceptional states equal H, and the own exceptional state vanishes. -/
theorem dependencies (i : Fin 2) :
    actual (curve i, .point) = actual (curve i, .hyperplane) ∧
    actual (curve i, .exceptional i) = 0 ∧
    actual (curve i, .exceptional i.rev) = actual (curve i, .point) := by
  have h₀ := equation i 0
  have h₁ := equation i 1
  have h₂ := equation i 2
  fin_cases i
  all_goals
    norm_num [Fin.sum_univ_five, fullCoefficients, canonicalFamily, Fin.rev,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four] at h₀ h₁ h₂ ⊢
    exact ⟨by linarith only [h₀], by linarith only [h₁], by linarith only [h₂]⟩

end AxiomaticGW.BlowupTwoRuling.BP
