/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHTwoFlagZero

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberHZeroValues
open SurfaceGenusTwo BlowupF1FiberHReduction BlowupF1FiberHZeroCoefficients
open BlowupF1FiberHTwoFlagZero
set_option maxRecDepth 20000

/-- The two-flag main component kills this complete original contraction for both requested labels. -/
theorem term52_zero (r : Fin 2) : weightedTerm (requested r) 52 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (52 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (52 : Fin 815) = L24Gluing.term52 from rfl]
  have hk : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term52, L24Gluing.expression13, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide), hk]
  apply Finset.sum_eq_zero
  intro split _
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij hij
  have hn : ij.2 ≤ 1 := by
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    omega
  apply mul_eq_zero_of_right
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro split' _
  apply Finset.sum_eq_zero
  intro b' _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro kl hkl
  have hm : kl.2 ≤ 1 := by
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
    omega
  apply mul_eq_zero_of_right
  apply mul_eq_zero_of_right
  exact remainder_two_flags_zero r kl.2 hm 0 _ _ _

/-- The original H0 contribution, with its complete signed weight unchanged. -/
theorem h_0052 : weightedTerm .hyperplane 52 = 0 := term52_zero 0

/-- The original K0 contribution, with its complete signed weight unchanged. -/
theorem k_0052 : weightedTerm (.exceptional 0) 52 = 0 := term52_zero 1

end AxiomaticGW.BlowupF1FiberHZeroValues
