/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.CurveConventionCertificate
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Tactic.LinearCombination

/-! # Multiple-cover edge factors for a surface GKM graph

The normal line of degree `a` pulls back to degree `d*a` on a cover of degree `d`.
For a nonnegative pullback degree the normal weights occur in the denominator,
including both endpoints. A negative degree uses only interior obstruction weights.
The deck group is counted separately when assembling the graph.
-/

@[expose] public section
namespace AxiomaticGW.GKM.SurfaceLocalizationEdge
open CurveConventionCertificate EquivariantCoefficients

variable {K : Type*} [Field K] [DecidableEq K]

/-- Normal contribution with oriented flag weight `u`, initial normal weight `n`
and pulled-back normal degree `k`. A zero deformation weight has no inverse. -/
def normal? (u n : K) : ℤ → Option K
  | .ofNat a =>
    let weights := ∏ j : Fin (a + 1), (n - (j.val : K) * u)
    if weights = 0 then none else some weights⁻¹
  | .negSucc a => some (∏ j : Fin a, (n + (j.val + 1 : K) * u))

/-- Reversing the oriented flag starts at the other end of the same normal line. -/
theorem normal_reverse (u n : K) (k : ℤ) :
    normal? (-u) (n - (k : K)*u) k = normal? u n k := by
  cases k with
  | ofNat a =>
    have weights :
        (∏ j : Fin (a+1), (n - (a : K)*u - (j.val : K)*(-u))) =
        ∏ j : Fin (a+1), (n - (j.val : K)*u) := by
      rw [← Equiv.prod_comp Fin.revPerm (fun j : Fin (a+1) ↦ n - (j.val : K)*u)]
      apply Finset.prod_congr rfl
      intro j _
      have hi : j.val + (Fin.revPerm j).val = a := by
        change j.val + (a + 1 - (j.val + 1)) = a
        omega
      have hc : (j.val : K) + ((Fin.revPerm j).val : K) = a := by
        rw [← Nat.cast_add, hi]
      linear_combination u * hc
    have cast : ((Int.ofNat a : ℤ) : K) = (a : K) := Int.cast_natCast a
    simp only [normal?, cast, weights]
  | negSucc a =>
    simp only [normal?]
    apply congrArg some
    rw [← Equiv.prod_comp Fin.revPerm (fun j : Fin a ↦ n + (j.val + 1 : K)*u)]
    apply Finset.prod_congr rfl
    intro j _
    have hi : j.val + 1 + ((Fin.revPerm j).val + 1) = a + 1 := by
      change j.val + 1 + (a - (j.val + 1) + 1) = a + 1
      omega
    have hc : (j.val : K) + 1 + (((Fin.revPerm j).val : K) + 1) = (a : K) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun z : ℕ ↦ (z : K)) hi
    simp only [Int.cast_negSucc, Nat.cast_add_one]
    linear_combination -u * hc

/-- The multiple-cover deformation and obstruction factor before division by deck symmetries. -/
def factor? (d : ℕ+) (w n : K) (a : ℤ) : Option K := do
  if w = 0 ∨ (d.val.factorial : K) = 0 then none else
    let u := w / (d.val : K)
    let b ← normal? u n ((d.val : ℤ) * a)
    return (-1 : K)^d.val / (d.val.factorial : K)^2 / u^(2*d.val) * b

/-- Changing the source endpoint negates the tangent and transports the normal weight
by the signed degree of the original normal line. The entire edge factor is invariant. -/
theorem factor_reverse [CharZero K] (d : ℕ+) (w n : K) (a : ℤ) :
    factor? d (-w) (n - (a : K)*w) a = factor? d w n a := by
  have hd : (d.val : K) ≠ 0 := Nat.cast_ne_zero.mpr d.ne_zero
  have hf : (d.val.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have transport : n - (a : K)*w = n - (((d.val : ℤ)*a : ℤ) : K) * (w / d.val) := by
    rw [Int.cast_mul, Int.cast_natCast, mul_comm (d.val : K), mul_assoc,
      mul_div_cancel₀ w hd]
  have even : (-(w / (d.val : K)))^(2*d.val) = (w / (d.val : K))^(2*d.val) := by
    rw [pow_mul, neg_sq, ← pow_mul]
  by_cases hw : w = 0
  · simp only [hw, neg_zero, factor?, true_or, if_true]
  · simp only [factor?, hw, neg_ne_zero.mpr hw, hf, or_self, if_false, neg_div, transport,
      normal_reverse, even]

/-- Read the oriented tangent, the transverse character and its signed degree from one
imported table entry. Both coefficient variables survive the evaluation. -/
noncomputable def atEdge? {X : SurfaceTarget} {v e : ℕ} (t : Tables X v e)
    (i : Fin e) (d : ℕ+) : Option Coefficient := by
  classical
  let edge := t.edges i
  exact factor? d (character edge.weight) (character (edgeWeight t edge.source edge.normalSource))
    edge.normalDegree

end AxiomaticGW.GKM.SurfaceLocalizationEdge
