/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.AffineEvaluation
public import AxiomaticGW.Surfaces.PlaneGenusTwoCoefficientReplay
public import AxiomaticGW.Surfaces.PlaneGenusTwoRecursion
public import AxiomaticGW.Surfaces.PlaneGenusTwoRemainder

/-!
# Scalar replay of the complete plane genus-two remainder

Canonical closure permits evaluation from one constant and finitely many
singleton coefficients at smaller degrees. Each scalar is identified with
the original normalized BP equation; no polynomial remainder is discarded.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction

private theorem earlier_injective (d : ℕ) : Function.Injective
    (fun p : Fin d × Fin 3 ↦ (Sum.inr (planeCanonicalQueries p.1.val p.2) : Variable .plane)) := by
  rintro ⟨b, j⟩ ⟨c, k⟩ he
  have hb := congrArg (fun v : Variable .plane ↦ SurfaceGenusZero.variableCurve v 0) he
  simp only [SurfaceGenusZero.variableCurve, planeCanonicalQueries_beta,
    Matrix.cons_val_zero] at hb
  have hbc : b = c := Fin.ext hb
  subst c
  exact Prod.ext rfl (planeCanonicalQueries_injective b.val (Sum.inr.inj he))

private def earlierVariables (d : ℕ) : Finset (Variable .plane) :=
  Finset.univ.image (fun p : Fin d × Fin 3 ↦ Sum.inr (planeCanonicalQueries p.1.val p.2))

private theorem remainder_support (d : ℕ) (hd : 0 < d) (i : Fin 3)
    (t : ℚ × Multiset (Variable .plane)) (ht : t ∈ planeShiftedRemainder d i) :
    t.2 = 0 ∨ ∃ v ∈ earlierVariables d, t.2 = {v} := by
  obtain ⟨hc, _⟩ := Multiset.mem_filter.mp ht
  obtain ⟨hm, _, _⟩ := RationalTerms.mem_collect.mp hc
  obtain ⟨u, hu, he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hm)
  rcases planeShiftedTerms_canonical_support d i hu with hz | ⟨b, j, hj⟩
  · exact Or.inl (he.symm.trans hz)
  · have htj := he.symm.trans hj
    obtain ⟨c, hcd, k, hk⟩ := planeShiftedRemainder_canonical_dependencies d hd i ht
      (Sum.inr (planeCanonicalQueries b j)) (by rw [htj]; exact Multiset.mem_singleton_self _)
    refine Or.inr ⟨Sum.inr (planeCanonicalQueries c k), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(⟨c, hcd⟩, k), Finset.mem_univ _, rfl⟩
    · rw [htj, hk]

/-- Earlier canonical coefficients are unchanged by collecting and isolating the current block. -/
theorem planeShiftedRemainder_coefficient (d b : ℕ) (hb : b < d) (i j : Fin 3) :
    RationalTerms.coefficient (planeShiftedRemainder d i) {Sum.inr (planeCanonicalQueries b j)} =
      RationalTerms.coefficient (planeShiftedTerms d i) {Sum.inr (planeCanonicalQueries b j)} := by
  rw [planeShiftedRemainder,
    RationalTerms.coefficient_filter _ (fun m ↦ ∀ v ∈ planeCanonicalVariables d, m ≠ {v}), if_pos,
    RationalTerms.coefficient_collect]
  intro v hv he
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
  have h := congrArg (fun v : Variable .plane ↦ SurfaceGenusZero.variableCurve v 0)
    (Multiset.singleton_inj.mp he)
  simp only [SurfaceGenusZero.variableCurve, planeCanonicalQueries_beta,
    Matrix.cons_val_zero] at h
  omega

/-- Exact finite scalar evaluation of every retained lower-degree dependency. -/
theorem eval_planeShiftedRemainder_finite (v : Variable .plane → ℚ) (d : ℕ) (hd : 0 < d)
    (i : Fin 3) :
    RationalTerms.eval v (planeShiftedRemainder d i) = planeShiftedConstant d i +
      ∑ b : Fin d, ∑ j : Fin 3,
        RationalTerms.coefficient (planeShiftedTerms d i)
          {Sum.inr (planeCanonicalQueries b.val j)} *
          v (Sum.inr (planeCanonicalQueries b.val j)) := by
  have hc : RationalTerms.eval (fun _ ↦ (0 : ℚ)) (planeShiftedRemainder d i) =
      planeShiftedConstant d i := by
    rw [planeShiftedConstant, eval_planeShiftedTerms]
    simp only [Matrix.mulVec, dotProduct, mul_zero, Finset.sum_const_zero, zero_add]
  rw [RationalTerms.eval_eq_constant_add_sum v _ (earlierVariables d)
    (remainder_support d hd i), hc, earlierVariables,
    Finset.sum_image (fun _ _ _ _ he ↦ earlier_injective d he)]
  simp only [Fintype.sum_prod_type, planeShiftedRemainder_coefficient d _ (Fin.isLt _)]

/-- One earlier coefficient extracted from the exact effective remainder. -/
def planeEarlierCoefficient (d : ℕ) (i : Fin 3) (b : ℕ) (j : Fin 3) : ℚ :=
  let v : Variable .plane := Sum.inr (planeCanonicalQueries b j)
  (![planeCachedPointCoefficient (3 * d + 1) (d + 1)
        ![.hyperplane, .hyperplane, .point] v,
      planeCachedPointCoefficient (3 * d) (d + 1) ![.hyperplane, .point, .point] v,
      planeCachedPointCoefficient (3 * d - 1) (d + 1) ![.point, .point, .point] v] :
    Fin 3 → ℚ) i

/-- Every scalar coefficient is bound to its full original equation and query. -/
theorem planeEarlierCoefficient_eq (d b : ℕ) (i j : Fin 3) :
    planeEarlierCoefficient d i b j = RationalTerms.coefficient (planeShiftedTerms d i)
      {Sum.inr (planeCanonicalQueries b j)} := by
  fin_cases i <;>
    exact (planeCachedPointCoefficient_eq _ _ _ _).trans
      ((planePointCoefficientByRemainder_eq _ _ _ _).trans (pointCoefficient_eq_full _ _ _ _ _))

/-- Replay the complete remainder using only earlier canonical values.
Zero values do not require computing their coefficients. -/
def planeScalarRemainder (values : ℕ → Fin 3 → ℚ) (d : ℕ) (i : Fin 3) : ℚ :=
  planeShiftedConstantFast d i +
    ∑ b : Fin d, ∑ j : Fin 3,
      if values b.val j = 0 then 0 else planeEarlierCoefficient d i b.val j * values b.val j

/-- Scalar replay preserves the entire collected remainder, including its constant. -/
theorem planeScalarRemainder_eq (values : ℕ → Fin 3 → ℚ) (d : ℕ) (hd : 0 < d) (i : Fin 3) :
    planeScalarRemainder values d i =
      RationalTerms.eval (planeCanonicalValuation values) (planeShiftedRemainder d i) := by
  rw [eval_planeShiftedRemainder_finite _ d hd i]
  have hskip (c x : ℚ) : (if x = 0 then 0 else c * x) = c * x := by
    by_cases hx : x = 0
    · rw [if_pos hx, hx, mul_zero]
    · exact if_neg hx
  simp only [planeScalarRemainder, planeShiftedConstantFast_eq, planeEarlierCoefficient_eq,
    planeCanonicalValuation_apply, hskip]

end AxiomaticGW.BelorousskiPandharipande
