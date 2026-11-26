/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.Term52
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.H0051

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberHZeroValues
open SurfaceGenusTwo BlowupF1FiberHReduction BlowupF1FiberHZeroCoefficients
open BlowupF1FiberHTwoFlagZero
-- Match the existing complete L24 frame elaboration depth.
set_option maxRecDepth 20000

/-- Vanishing of the exact two-flag main coefficient before rational complements are evaluated. -/
theorem term51_zero (r : Fin 2) : weightedTerm (requested r) 51 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (51 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (51 : Fin 815) = L24Gluing.term51 from rfl]
  have hk : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term51, L24Gluing.expression12, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
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
  exact remainder_two_flags_zero r ij.2 hn 1 _ _ _

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem k_0051 : weightedTerm (.exceptional 0) 51 = 0 := term51_zero 1

/-- Vanishing of the exact two-flag main coefficient before rational complements are evaluated. -/
theorem term57_zero (r : Fin 2) : weightedTerm (requested r) 57 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (57 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (57 : Fin 815) = L24Gluing.term57 from rfl]
  have hk : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term57, L24Gluing.expression15, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
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
  exact remainder_two_flags_zero r ij.2 hn 0 _ _ _

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem h_0057 : weightedTerm .hyperplane 57 = 0 := term57_zero 0

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem k_0057 : weightedTerm (.exceptional 0) 57 = 0 := term57_zero 1

/-- Vanishing of the exact two-flag main coefficient before rational complements are evaluated. -/
theorem term59_zero (r : Fin 2) : weightedTerm (requested r) 59 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (59 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (59 : Fin 815) = L24Gluing.term59 from rfl]
  have hk : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term59, L24Gluing.expression16, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
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
  exact remainder_two_flags_zero r ij.2 hn 0 _ _ _

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem h_0059 : weightedTerm .hyperplane 59 = 0 := term59_zero 0

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem k_0059 : weightedTerm (.exceptional 0) 59 = 0 := term59_zero 1

/-- Vanishing of the exact two-flag main coefficient before rational complements are evaluated. -/
theorem term62_zero (r : Fin 2) : weightedTerm (requested r) 62 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (62 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (62 : Fin 815) = L24Gluing.term62 from rfl]
  have hk : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term62, L24Gluing.expression17, GetzlerGraphs.join,
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
  exact remainder_two_flags_zero r kl.2 hm 1 _ _ _

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem h_0062 : weightedTerm .hyperplane 62 = 0 := term62_zero 0

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem k_0062 : weightedTerm (.exceptional 0) 62 = 0 := term62_zero 1

/-- Vanishing of the exact two-flag main coefficient before rational complements are evaluated. -/
theorem term64_zero (r : Fin 2) : weightedTerm (requested r) 64 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (64 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (64 : Fin 815) = L24Gluing.term64 from rfl]
  have hk : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term64, L24Gluing.expression19, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
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
  exact remainder_two_flags_zero r ij.2 hn 0 _ _ _

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem h_0064 : weightedTerm .hyperplane 64 = 0 := term64_zero 0

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem k_0064 : weightedTerm (.exceptional 0) 64 = 0 := term64_zero 1

/-- Vanishing of the exact two-flag main coefficient before rational complements are evaluated. -/
theorem term66_zero (r : Fin 2) : weightedTerm (requested r) 66 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (66 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (66 : Fin 815) = L24Gluing.term66 from rfl]
  have hk : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term66, L24Gluing.expression20, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
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
  exact remainder_two_flags_zero r ij.2 hn 0 _ _ _

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem h_0066 : weightedTerm .hyperplane 66 = 0 := term66_zero 0

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem k_0066 : weightedTerm (.exceptional 0) 66 = 0 := term66_zero 1

/-- Vanishing of the exact two-flag main coefficient before rational complements are evaluated. -/
theorem term69_zero (r : Fin 2) : weightedTerm (requested r) 69 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (69 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (69 : Fin 815) = L24Gluing.term69 from rfl]
  have hk : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term69, L24Gluing.expression21, GetzlerGraphs.join,
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
  exact remainder_two_flags_zero r kl.2 hm 1 _ _ _

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem h_0069 : weightedTerm .hyperplane 69 = 0 := term69_zero 0

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem k_0069 : weightedTerm (.exceptional 0) 69 = 0 := term69_zero 1

/-- Vanishing of the exact two-flag main coefficient before rational complements are evaluated. -/
theorem term76_zero (r : Fin 2) : weightedTerm (requested r) 76 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (76 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (76 : Fin 815) = L24Gluing.term76 from rfl]
  have hk : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term76, L24Gluing.expression24, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
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
  exact remainder_two_flags_zero r ij.2 hn 1 _ _ _

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem h_0076 : weightedTerm .hyperplane 76 = 0 := term76_zero 0

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem k_0076 : weightedTerm (.exceptional 0) 76 = 0 := term76_zero 1

/-- Vanishing of the exact two-flag main coefficient before rational complements are evaluated. -/
theorem term83_zero (r : Fin 2) : weightedTerm (requested r) 83 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (83 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (83 : Fin 815) = L24Gluing.term83 from rfl]
  have hk : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term83, L24Gluing.expression27, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
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
  exact remainder_two_flags_zero r ij.2 hn 1 _ _ _

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem h_0083 : weightedTerm .hyperplane 83 = 0 := term83_zero 0

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem k_0083 : weightedTerm (.exceptional 0) 83 = 0 := term83_zero 1

/-- Vanishing of the exact two-flag main coefficient before rational complements are evaluated. -/
theorem term93_zero (r : Fin 2) : weightedTerm (requested r) 93 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (93 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (93 : Fin 815) = L24Gluing.term93 from rfl]
  have hk : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term93, L24Gluing.expression31, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
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
  exact remainder_two_flags_zero r ij.2 hn 0 _ _ _

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem h_0093 : weightedTerm .hyperplane 93 = 0 := term93_zero 0

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem k_0093 : weightedTerm (.exceptional 0) 93 = 0 := term93_zero 1

/-- Vanishing of the exact two-flag main coefficient before rational complements are evaluated. -/
theorem term95_zero (r : Fin 2) : weightedTerm (requested r) 95 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (95 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (95 : Fin 815) = L24Gluing.term95 from rfl]
  have hk : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by
    funext i
    fin_cases i <;> rfl
  simp only [L24Gluing.term95, L24Gluing.expression32, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
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
  exact remainder_two_flags_zero r ij.2 hn 0 _ _ _

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem h_0095 : weightedTerm .hyperplane 95 = 0 := term95_zero 0

/-- The original weighted contribution; all labels and the source class are unchanged. -/
theorem k_0095 : weightedTerm (.exceptional 0) 95 = 0 := term95_zero 1

/-- A primary genus-two main component has zero coefficient at either nonprimary request. -/
theorem term109_zero (r : Fin 2) : weightedTerm (requested r) 109 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (109 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (109 : Fin 815) = L24Gluing.term109 from rfl,
    firstCoefficientVertex_eq]
  change remainderPointCoefficient target (zeroVariable (requested r))
    (coefficientVertex target (zeroVariable (requested r))) L24Gluing.term109
    ![1, 1] 1 _ = 0
  have hv : ∀ beta m, Sum.inr (SurfaceQuery.points target 2 beta m) ≠
      zeroVariable (requested r) := fun beta m ↦
    SurfaceFirstDescendant.query_ne_points 0 beta (requested r) 0 m
  have hk : (![0] : Fin 1 → ℕ) = 0 := by
    funext i
    fin_cases i
    rfl
  simp only [L24Gluing.term109, L24Gluing.expression39, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide), hk,
    remainderVertex_primary_eq_zero_of_not_points (zeroVariable (requested r)) hv,
    mul_zero, zero_mul, Finset.sum_const_zero]

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem h_0109 : weightedTerm .hyperplane 109 = 0 := term109_zero 0

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem k_0109 : weightedTerm (.exceptional 0) 109 = 0 := term109_zero 1

/-- A primary genus-two main component has zero coefficient at either nonprimary request. -/
theorem term110_zero (r : Fin 2) : weightedTerm (requested r) 110 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (110 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (110 : Fin 815) = L24Gluing.term110 from rfl,
    firstCoefficientVertex_eq]
  change remainderPointCoefficient target (zeroVariable (requested r))
    (coefficientVertex target (zeroVariable (requested r))) L24Gluing.term110
    ![1, 1] 1 _ = 0
  have hv : ∀ beta m, Sum.inr (SurfaceQuery.points target 2 beta m) ≠
      zeroVariable (requested r) := fun beta m ↦
    SurfaceFirstDescendant.query_ne_points 0 beta (requested r) 0 m
  have hk : (![0] : Fin 1 → ℕ) = 0 := by
    funext i
    fin_cases i
    rfl
  simp only [L24Gluing.term110, L24Gluing.expression40, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide), hk,
    remainderVertex_primary_eq_zero_of_not_points (zeroVariable (requested r)) hv,
    mul_zero, zero_mul, Finset.sum_const_zero]

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem h_0110 : weightedTerm .hyperplane 110 = 0 := term110_zero 0

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem k_0110 : weightedTerm (.exceptional 0) 110 = 0 := term110_zero 1

/-- A primary genus-two main component has zero coefficient at either nonprimary request. -/
theorem term112_zero (r : Fin 2) : weightedTerm (requested r) 112 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (112 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (112 : Fin 815) = L24Gluing.term112 from rfl,
    firstCoefficientVertex_eq]
  change remainderPointCoefficient target (zeroVariable (requested r))
    (coefficientVertex target (zeroVariable (requested r))) L24Gluing.term112
    ![1, 1] 1 _ = 0
  have hv : ∀ beta m, Sum.inr (SurfaceQuery.points target 2 beta m) ≠
      zeroVariable (requested r) := fun beta m ↦
    SurfaceFirstDescendant.query_ne_points 0 beta (requested r) 0 m
  have hk : (![0] : Fin 1 → ℕ) = 0 := by
    funext i
    fin_cases i
    rfl
  simp only [L24Gluing.term112, L24Gluing.expression42, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide), hk,
    remainderVertex_primary_eq_zero_of_not_points (zeroVariable (requested r)) hv,
    mul_zero, zero_mul, Finset.sum_const_zero]

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem h_0112 : weightedTerm .hyperplane 112 = 0 := term112_zero 0

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem k_0112 : weightedTerm (.exceptional 0) 112 = 0 := term112_zero 1

/-- A primary genus-two main component has zero coefficient at either nonprimary request. -/
theorem term113_zero (r : Fin 2) : weightedTerm (requested r) 113 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (113 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (113 : Fin 815) = L24Gluing.term113 from rfl,
    firstCoefficientVertex_eq]
  change remainderPointCoefficient target (zeroVariable (requested r))
    (coefficientVertex target (zeroVariable (requested r))) L24Gluing.term113
    ![1, 1] 1 _ = 0
  have hv : ∀ beta m, Sum.inr (SurfaceQuery.points target 2 beta m) ≠
      zeroVariable (requested r) := fun beta m ↦
    SurfaceFirstDescendant.query_ne_points 0 beta (requested r) 0 m
  have hk : (![0] : Fin 1 → ℕ) = 0 := by
    funext i
    fin_cases i
    rfl
  simp only [L24Gluing.term113, L24Gluing.expression43, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide), hk,
    remainderVertex_primary_eq_zero_of_not_points (zeroVariable (requested r)) hv,
    mul_zero, zero_mul, Finset.sum_const_zero]

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem h_0113 : weightedTerm .hyperplane 113 = 0 := term113_zero 0

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem k_0113 : weightedTerm (.exceptional 0) 113 = 0 := term113_zero 1

/-- A primary genus-two main component has zero coefficient at either nonprimary request. -/
theorem term119_zero (r : Fin 2) : weightedTerm (requested r) 119 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (119 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (119 : Fin 815) = L24Gluing.term119 from rfl,
    firstCoefficientVertex_eq]
  change remainderPointCoefficient target (zeroVariable (requested r))
    (coefficientVertex target (zeroVariable (requested r))) L24Gluing.term119
    ![1, 1] 1 _ = 0
  have hv : ∀ beta m, Sum.inr (SurfaceQuery.points target 2 beta m) ≠
      zeroVariable (requested r) := fun beta m ↦
    SurfaceFirstDescendant.query_ne_points 0 beta (requested r) 0 m
  have hk : (![0] : Fin 1 → ℕ) = 0 := by
    funext i
    fin_cases i
    rfl
  simp only [L24Gluing.term119, L24Gluing.expression49, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide), hk,
    remainderVertex_primary_eq_zero_of_not_points (zeroVariable (requested r)) hv,
    mul_zero, zero_mul, Finset.sum_const_zero]

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem h_0119 : weightedTerm .hyperplane 119 = 0 := term119_zero 0

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem k_0119 : weightedTerm (.exceptional 0) 119 = 0 := term119_zero 1

/-- A primary genus-two main component has zero coefficient at either nonprimary request. -/
theorem term120_zero (r : Fin 2) : weightedTerm (requested r) 120 = 0 := by
  unfold weightedTerm
  suffices hz : remainderPointCoefficient target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) (L24Gluing.term (120 : Fin 815))
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 by
    rw [hz, mul_zero]
  rw [show L24Gluing.term (120 : Fin 815) = L24Gluing.term120 from rfl,
    firstCoefficientVertex_eq]
  change remainderPointCoefficient target (zeroVariable (requested r))
    (coefficientVertex target (zeroVariable (requested r))) L24Gluing.term120
    ![1, 1] 1 _ = 0
  have hv : ∀ beta m, Sum.inr (SurfaceQuery.points target 2 beta m) ≠
      zeroVariable (requested r) := fun beta m ↦
    SurfaceFirstDescendant.query_ne_points 0 beta (requested r) 0 m
  have hk : (![0] : Fin 1 → ℕ) = 0 := by
    funext i
    fin_cases i
    rfl
  simp only [L24Gluing.term120, L24Gluing.expression50, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide), hk,
    remainderVertex_primary_eq_zero_of_not_points (zeroVariable (requested r)) hv,
    mul_zero, zero_mul, Finset.sum_const_zero]

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem h_0120 : weightedTerm .hyperplane 120 = 0 := term120_zero 0

/-- The original primary-main contribution, proved zero with the existing coefficient API. -/
theorem k_0120 : weightedTerm (.exceptional 0) 120 = 0 := term120_zero 1

end AxiomaticGW.BlowupF1FiberHZeroValues
