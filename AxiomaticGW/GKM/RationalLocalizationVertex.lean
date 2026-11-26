/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.PointTarget.GenusZeroMultinomial
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-! # Rational source vertices with arbitrary descendants and flags

The multinomial theorem collects the flag powers into one power of the sum of
reciprocal characters. The coefficient retains every externally marked cotangent
power. Stability and the curve geometry enter when the sum is evaluated on actual
intersection numbers. The tangent normalization and target insertions are external.
-/

@[expose] public section
namespace AxiomaticGW.GKM.RationalLocalizationVertex
open PsiBoundaryExpansion

variable {L : Type*} [Field L] {a f : ℕ}

/-- Exact-weight expansion used by a stable rational vertex on a surface. -/
def source (d : Fin a → ℕ) (u v : L) (w : Fin f → L) (H : ((Fin a ⊕ Fin f) → ℕ) → ℚ) : L :=
  let dim := a + f - 3
  let used := ∑ s, d s
  if used ≤ dim then (u * v)⁻¹ *
    ∑ k ∈ Finset.piAntidiag Finset.univ (dim - used),
      (H (Sum.elim d k) : L) * ∏ s, w s ^ (-(k s : ℤ) - 1)
  else 0

/-- Closed expression for all markings and valences, including no remaining flag power. -/
def closed (d : Fin a → ℕ) (u v : L) (w : Fin f → L) : L :=
  let dim := a + f - 3
  let used := ∑ s, d s
  let left := dim - used
  if used ≤ dim then (u * v)⁻¹ *
    (((dim.factorial : L) / ((left.factorial : L) * ∏ s, ((d s).factorial : L))) *
      (∏ s, (w s)⁻¹) * (∑ s, (w s)⁻¹) ^ left)
  else 0

private theorem flag_product (w : Fin f → L) (k : Fin f → ℕ) :
    (∏ s, w s ^ (-(k s : ℤ) - 1)) = (∏ s, (w s)⁻¹) * ∏ s, (w s)⁻¹ ^ k s := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s _
  rw [show -(k s : ℤ) - 1 = -((k s + 1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, pow_succ, mul_inv_rev, inv_pow]

private theorem coefficient [CharZero L] (dim r : ℕ) (d : Fin a → ℕ) (k : Fin f → ℕ)
    (hk : ∑ s, k s = r) :
    (dim.factorial : L) / ((∏ s, ((d s).factorial : L)) * ∏ s, ((k s).factorial : L)) =
      (dim.factorial : L) / ((r.factorial : L) * ∏ s, ((d s).factorial : L)) *
        (Nat.multinomial Finset.univ k : L) := by
  have hprod : (∏ s, ((k s).factorial : L)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s _ ↦ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfact : (r.factorial : L) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hmul := congrArg (Nat.cast : ℕ → L) (Nat.multinomial_spec Finset.univ k)
  simp only [hk, Nat.cast_mul, Nat.cast_prod] at hmul
  have hval : (Nat.multinomial Finset.univ k : L) =
      (r.factorial : L) / ∏ s, ((k s).factorial : L) :=
    (eq_div_iff hprod).mpr ((mul_comm ..).trans hmul)
  rw [hval]
  field_simp

/-- The geometric genus-zero integral of the dimension-selected source equals the closed
expression. In localization all weights occurring in denominators are nonzero. -/
theorem source_eq_closed [CharZero L] {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C}
    (U : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (T : TailForgetCompatible C)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1) (h : StableArity 0 (Fin a ⊕ Fin f))
    (d : Fin a → ℕ) (u v : L) (w : Fin f → L) :
    source d u v w (PointTarget.intersectionNumber P I 0 _) = closed d u v w := by
  unfold source closed
  dsimp only
  split
  next hd =>
    congr 1
    rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have ht : (∑ s, k s) = a + f - 3 - ∑ s, d s := (Finset.mem_piAntidiag.mp hk).1
    have hdim : (∑ s, Sum.elim d k s) = Fintype.card (Fin a ⊕ Fin f) - 3 := by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.card_sum,
        Fintype.card_fin, ht]
      exact Nat.add_sub_of_le hd
    rw [PointTarget.genusZero_intersection_of_geometry U F N P K hK T vol h _, if_pos hdim]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.prod_sum_type, Sum.elim_inl,
      Sum.elim_inr, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod]
    rw [coefficient _ _ d k ht, flag_product]
    ac_rfl
  next => rfl

end AxiomaticGW.GKM.RationalLocalizationVertex
