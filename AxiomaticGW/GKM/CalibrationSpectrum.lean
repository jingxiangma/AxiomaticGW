/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.FirstOrderFixedPoints
public import Mathlib.Tactic.FieldSimp

/-! # Localization of a primitive-degree descendant calibration at its two loop expansions -/

@[expose] public section
namespace AxiomaticGW.GKM.CalibrationSpectrum
open Matrix
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- Pull both slots of a paired two-point tensor back along a basis matrix. -/
def pull (V F : Matrix I I K) : Matrix I I K := V.transpose * F * V

/-- The undeformed divisor matrix is diagonal in the fixed-point frame. -/
theorem conjugate_cup (P V C : Matrix I I K) (χ : I → K) (hVP : V * P = 1)
    (hPV : P * V = 1) (h : P * C = diagonal χ * P) : C * V = V * diagonal χ := by
  calc C * V = V * (P * C) * V := by rw [← Matrix.mul_assoc, hVP, one_mul]
       _ = V * diagonal χ := by simp only [h, Matrix.mul_assoc, hPV, mul_one]

/-- Transform an anticanonical commutator recurrence for the two lower indices. -/
theorem pull_commutator (V C F G : Matrix I I K) (χ : I → K) (n : K)
    (h : C * V = V * diagonal χ) (hrec : n • G = C.transpose * F - F * C) (i j : I) :
    n * pull V G i j = (χ i - χ j) * pull V F i j := by
  have ht := congrArg transpose h
  simp only [transpose_mul, diagonal_transpose] at ht
  have hm : n • pull V G = diagonal χ * pull V F - pull V F * diagonal χ := by
    unfold pull
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hrec, mul_sub, sub_mul]
    congr 1
    · simp only [← Matrix.mul_assoc, ht]
    · simp only [Matrix.mul_assoc, h]
  have hij := congrFun (congrFun hm i) j
  simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, diagonal_mul, mul_diagonal,
    sub_mul, mul_comm (χ j)] using hij

open FirstOrderFixedPoints
variable {D E : Type*} [Fintype E]

def edgeRow (P : Matrix I I K) (p : Pair I) : I → K := fun i ↦ p.diff (P.col i)

def divisorForm (P : Matrix I I K) (p : E → Pair I) (w : D → E → K)
    (d : D) (χ : I → K) : Matrix I I K :=
  ∑ t, (w d t * (p t).diff χ) • vecMulVec (edgeRow P (p t)) (edgeRow P (p t))

omit [DecidableEq I] in
theorem edgeRow_mul (P V : Matrix I I K) (p : Pair I) :
    edgeRow P p ᵥ* V = edgeRow (P * V) p := by
  funext j
  simp only [edgeRow, Pair.diff, Matrix.col_apply, Matrix.mul_apply, vecMul,
    dotProduct, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq I] in
theorem divisorForm_pull (P V : Matrix I I K) (p : E → Pair I) (w : D → E → K) (d : D)
    (χ : I → K) : V.transpose * divisorForm P p w d χ * V = divisorForm (P * V) p w d χ := by
  simp only [divisorForm, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_vecMulVec, vecMulVec_mul, mulVec_transpose, edgeRow_mul]

omit [DecidableEq I] in
theorem divisorForm_apply (P : Matrix I I K) (p : E → Pair I) (w : D → E → K) (d : D)
    (c : I → K) (i j : I) :
    divisorForm P p w d (P *ᵥ c) i j =
      ∑ h, c h * cubic p w d (P.col h) (P.col i) (P.col j) := by
  simp only [divisorForm, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
    edgeRow, cubic, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  have h : (p t).diff (P *ᵥ c) = ∑ h, c h * (p t).diff (P.col h) := by
    simp only [Pair.diff, Matrix.mulVec, dotProduct, Matrix.col_apply, mul_sub,
      Finset.sum_sub_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [h]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [Fintype I] in
/-- The off-diagonal matrix coefficient of multiplication by the anticanonical class
is the spectral gap times the infinitesimal fixed-point change of coordinates. -/
theorem off_diagonal (e χ : I → K) (p : E → Pair I) (w : D → E → K) (d : D)
    (i j : I) (hij : i ≠ j) :
    e i * divisorForm 1 p w d χ i j = (χ i - χ j) * changeOfBasis e p w d (Pi.single j 1) i := by
  simp only [divisorForm, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
    changeOfBasis, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [edgeRow, Pair.diff, Matrix.col_apply, Matrix.one_apply, Pi.single_apply]
  generalize (p t).left = l
  generalize (p t).right = r
  split_ifs <;> subst_vars <;> (try contradiction) <;> ring

/-- The coefficients about infinity of A/(z-t), indexed by the retained cotangent power. -/
def infinityCoefficient (A t : K) (m : ℕ) : K := t^m * A

theorem infinity_succ (A t : K) (m : ℕ) :
    infinityCoefficient A t (m+1) = t * infinityCoefficient A t m := by
  simp only [infinityCoefficient, pow_succ]
  ring

/-- At a nonzero eigenvalue gap the constant and linear Taylor coefficients at zero
are fixed by the numerator and gap. The exact remainder starts in degree two. -/
theorem at_zero (A t z : K) (ht : t ≠ 0) :
    (z - t) * (-A/t + z * (-A/t^2)) = A - z^2 * A/t^2 := by
  field_simp
  ring

/-- Coefficient of z^m in the expansion of A/(z−t) at a nonzero gap t. -/
def taylorCoefficient (A t : K) (m : ℕ) : K := -A / t^(m + 1)

/-- Clearing z−t records the exact remainder of the Taylor polynomial at every order. -/
theorem taylor_remainder (A t z : K) (ht : t ≠ 0) (n : ℕ) :
    (z-t) * ∑ m ∈ Finset.range n, z^m * taylorCoefficient A t m = A - z^n*A/t^n := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero, one_mul, div_one,
      sub_self]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [taylorCoefficient, pow_succ]
    field_simp
    ring

/-- Interchanging the two fixed points reverses the gap, with this sign at power m. -/
theorem taylor_neg_gap (A t : K) (m : ℕ) :
    taylorCoefficient A (-t) m = (-1)^(m+1) * taylorCoefficient A t m := by
  simp only [taylorCoefficient, div_eq_mul_inv, ← inv_pow, inv_neg,
    neg_eq_neg_one_mul t⁻¹, mul_pow]
  ring

theorem at_zero_unique (A t a b : K) (ht : t ≠ 0)
    (h0 : -t * a = A) (h1 : a - t * b = 0) : a = -A/t ∧ b = -A/t^2 := by
  constructor
  · field_simp
    linear_combination -h0
  · field_simp
    linear_combination -h0 - t*h1

/-- A diagonal change in the first positive-loop coefficient commutes with the classical
spectrum and preserves the linear symplecticity equation. -/
theorem diagonal_freedom {R : Type*} [CommRing R] (g χ c : I → R) (B : Matrix I I R)
    (h : diagonal g * B = B.transpose * diagonal g) :
    diagonal χ * diagonal c = diagonal c * diagonal χ ∧
      diagonal g * (B + diagonal c) = (B + diagonal c).transpose * diagonal g := by
  constructor
  · simp only [diagonal_mul_diagonal, mul_comm]
  · rw [mul_add, transpose_add, add_mul, diagonal_transpose, h]
    simp only [diagonal_mul_diagonal, mul_comm]

/-- The exact quadratic remainder when a positive-loop series is inverted through
linear order. The coefficient matrix may be noncommutative. -/
theorem inverse_first_loop {K : Type*} [CommRing K] (B : Matrix I I K) (z : K) :
    (1 + z • B) * (1 - z • B) = 1 - z^2 • (B * B) := by
  simp only [add_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
  abel

/-- For the flat-unit convention z(1−R(z)⁻¹)1 the coefficient at z² is B1.
A diagonal gauge shift changes it by its diagonal entries. -/
theorem translation_shift (B : Matrix I I K) (c : I → K) :
    (B + diagonal c) *ᵥ 1 = B *ᵥ 1 + c := by
  rw [Matrix.add_mulVec]
  congr 1
  funext i
  simp only [mulVec_diagonal, Pi.one_apply, mul_one]

end AxiomaticGW.GKM.CalibrationSpectrum
