/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberTable

/-! # The original genus-two equations at the pullback line on the one-point blowup

At energy three the six full effective classes are 0, E, F, 2E, 3E, and H = E+F.
The certified energy-two table determines the first four, and exceptional-image
support determines 3E. Only the four canonical states at H remain in these equations.
-/

@[expose] public section
namespace AxiomaticGW.F1PlaneLine
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupScalar
open SurfaceGenusTwoBlowupBoundedCertificate
abbrev X := SurfaceTarget.hirzebruchOne

/-- Effective coordinates in the basis E, F with F = H − E. -/
def line : X.Curve := ![1, 1]

/-- Order of the four canonical queries in the producer exchange. -/
def families : Fin 4 → Family X := ![.hyperplane, .point, .primary, .exceptional 0]

private def curves : Fin 6 → X.Curve := ![0, ![1,0], ![0,1], ![2,0], ![3,0], line]
private def column (k : Fin 6 × Fin 4) : Variable X := .inr ((families k.2).query (curves k.1))

set_option maxRecDepth 20000

/-- All 24 states, including the nominal class-zero point-descendant slot. -/
theorem states_length : (states X 3).length = 24 := by decide +kernel

private theorem grid : columns (states X 3) = Finset.univ.image column := by decide +kernel
private theorem distinct : Function.Injective column := by
  change ∀ j k, column j = column k → j = k
  decide +kernel

abbrev value := SurfaceGenusTwoBlowupRecursion.values (X := X) 0

private theorem zero_values (j : Fin 4) :
    value (curves 0, families j) = (![-1/960, 0, 0, -1/2880] : Fin 4 → ℚ) j := by
  unfold value
  rw [BlowupF1FiberTable.values_eq _ (by change X.effective.energy (curves 0) ≤ 2; decide +kernel)]
  fin_cases j <;> decide +kernel

private theorem known (k : Fin 3) (j : Fin 4) :
    value (curves ⟨k.val+1, by omega⟩, families j) = 0 := by
  unfold value
  rw [BlowupF1FiberTable.values_eq _ (by
    change X.effective.energy (curves ⟨k.val + 1, by omega⟩) ≤ 2
    fin_cases k <;> decide +kernel)]
  fin_cases k <;> fin_cases j <;> decide +kernel

private theorem triple_exceptional (j : Fin 4) : value (curves 4, families j) = 0 := by
  unfold value
  rw [SurfaceGenusTwoBlowupRecursion.values_boundary _ _ (by
    change X.planeDegree (curves 4) = 0
    decide +kernel)]
  fin_cases j <;> decide +kernel

private theorem sum_six (f : Fin 6 → ℚ) : (∑ j, f j) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_four]
  change f 0 + (f 1 + (f 2 + f 3 + f 4 + f 5)) = _
  ring

/-- The original row after substituting all previously determined states. No values at H
are supplied as inputs, and the L24 hyperplane row uses its original shifted source. -/
theorem reduced_row (f : Family X) :
    constant 0 (line, f) -
      singletonCoefficient 0 (line, f) (.inr ((Family.hyperplane : Family X).query 0)) / 960 -
      singletonCoefficient 0 (line, f) (.inr ((Family.exceptional (X := X) 0).query 0)) / 2880 +
      ∑ b : Fin 4, singletonCoefficient 0 (line, f) (.inr ((families b).query line)) *
        value (line, families b) = 0 := by
  have hd : 0 < X.planeDegree line := by decide +kernel
  have hs : (line, f) ∈ states X 3 :=
    (mem_states X 3 _).mpr (by change X.effective.energy line ≤ 3; decide +kernel)
  have hr := (replay_eq_row 0 3 (line, f) (canonicalValuation value) hs hd).trans
    (SurfaceGenusTwoBlowupRecursion.values_equations 0 _ hd)
  have hm (a b : ℚ) : (if b = 0 then 0 else a * b) = a * b := by
    split_ifs with hb
    · rw [hb, mul_zero]
    · rfl
  rw [SurfaceGenusTwoBlowupScalar.replay, grid, Finset.sum_image
    (fun _ _ _ _ h ↦ distinct h), Fintype.sum_prod_type] at hr
  simp only [hm, column, canonicalValuation_query] at hr
  change constant 0 (line, f) + (∑ c : Fin 6, ∑ b : Fin 4,
    singletonCoefficient 0 (line, f) (.inr ((families b).query (curves c))) *
      value (curves c, families b)) = 0 at hr
  have h1 (b : Fin 4) : value (curves 1, families b) = 0 := known 0 b
  have h2 (b : Fin 4) : value (curves 2, families b) = 0 := known 1 b
  have h3 (b : Fin 4) : value (curves 3, families b) = 0 := known 2 b
  rw [sum_six] at hr
  simp only [h1, h2, h3, triple_exceptional, zero_values, mul_zero, Finset.sum_const_zero,
    add_zero] at hr
  have hz (g : Fin 4 → ℚ) : (∑ b, g b * (![-1/960, 0, 0, -1/2880] : Fin 4 → ℚ) b) =
      -g 0 / 960 - g 3 / 2880 := by
    rw [Fin.sum_univ_four]
    change g 0 * (-1 / 960) + g 1 * 0 + g 2 * 0 + g 3 * (-1 / 2880) = _
    ring
  rw [hz] at hr
  change constant 0 (line, f) + (-_ / 960 - _ / 2880 + _) = 0 at hr
  change constant 0 (line, f) -
    singletonCoefficient 0 (line, f) (.inr ((families 0).query (curves 0))) / 960 -
    singletonCoefficient 0 (line, f) (.inr ((families 3).query (curves 0))) / 2880 +
    ∑ b : Fin 4, singletonCoefficient 0 (line, f) (.inr ((families b).query (curves 5))) *
      value (curves 5, families b) = 0
  linarith only [hr]

end AxiomaticGW.F1PlaneLine
