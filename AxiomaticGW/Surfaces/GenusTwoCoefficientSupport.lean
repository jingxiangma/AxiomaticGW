/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPointCoefficients

/-!
# Full-class support of genus-two coefficients

Normalized coefficients vanish unless the requested curve class is a
coordinatewise effective part of the input. This applies to arbitrary
cotangent powers and to every signed additional-point pullback.
-/

@[expose] public section

namespace AxiomaticGW.SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)
variable {X : SurfaceTarget}

/-- Normalization removes only effective classes, including calibration tails. -/
theorem coefficient_normalizedTerms_eq_zero_of_not_le (q : SurfaceAncestorKey X)
    (hg : 2 ≤ q.genus) (v : Variable X) (hv : ¬variableCurve v ≤ q.beta) :
    RationalTerms.coefficient (normalizedTerms q) {v} = 0 := by
  unfold RationalTerms.coefficient
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
  apply if_neg
  intro he
  obtain ⟨w, hw, _, _, delta, hb⟩ := normalizedTerms_support q hg ht
  have h : w = v := Multiset.singleton_inj.mp (hw.symm.trans he)
  subst w
  apply hv
  intro i
  have hi := congrFun hb i
  change variableCurve v i + delta i = q.beta i at hi
  exact (Nat.le_add_right (variableCurve v i) (delta i)).trans_eq hi

end AxiomaticGW.SurfacePolynomialReduction

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)
variable {X : SurfaceTarget}

/-- The complete normalized expression preserves every effective coordinate. -/
theorem TermsBound.normalized_coefficient_eq_zero_of_not_le {g : ℕ}
    {beta : X.Curve} {p : RationalTerms (SurfaceAncestorKey X)}
    (hp : TermsBound g beta p) (hg : g ≤ 2) (v : Variable X)
    (hv : ¬variableCurve v ≤ beta) :
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms p) {v} = 0 := by
  rw [RationalTerms.coefficient_affineSubstitute_singleton]
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
  rcases ((hp.mono hg) t ht).affine with hz | ⟨q, hq, hgen, _, delta, hdelta⟩
  · rw [hz, Multiset.map_zero, Multiset.sum_zero, mul_zero]
  · rw [hq, Multiset.map_singleton, Multiset.sum_singleton,
      coefficient_normalizedTerms_eq_zero_of_not_le q (by omega) v, mul_zero]
    intro hle
    apply hv
    intro i
    have hi := congrFun hdelta i
    change q.beta i + delta i = beta i at hi
    exact (hle i).trans ((Nat.le_add_right (q.beta i) (delta i)).trans_eq hi)

/-- Support for the exact coefficient of a complete decorated contraction. -/
theorem normalizedCoefficient_eq_zero_of_not_le (v : Variable X)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g ≤ 2)
    (d : x.CotangentDecoration) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) (hv : ¬variableCurve v ≤ beta) :
    normalizedCoefficient x d beta k a v = 0 :=
  (termsBound_decorated x d beta k a).normalized_coefficient_eq_zero_of_not_le hg v hv

/-- Signed point pullbacks cannot create a larger or incomparable curve class. -/
theorem pointCoefficient_eq_zero_of_not_le (v : Variable X)
    {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm 2 S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X)
    (hv : ¬variableCurve v ≤ beta) :
    pointCoefficient X v z beta n a = 0 := by
  rw [pointCoefficient_eq]
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, _, rfl⟩ := Multiset.mem_map.mp hc
  rw [normalizedCoefficient_eq_zero_of_not_le v t.2.expression le_rfl _ _ _ _ hv, mul_zero]

/-- The compressed contraction has the same full-class support whenever it
contains the unique genus-two component. -/
theorem pointContraction_eq_zero_of_not_le (v : Variable X)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g ≤ 2)
    (hx : x.maxComponentGenus = 2) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X)
    (hv : ¬variableCurve v ≤ beta) :
    x.pointContraction X (SurfacePointPullback.vertex X (coefficientVertex X v))
      d l beta n a = 0 := by
  have hgen : g = 2 := le_antisymm hg (hx ▸ x.maxComponentGenus_le)
  subst g
  have he := pointCoefficient_eq_zero_of_not_le v ⟨x, d, l⟩ beta n a hv
  simpa only [pointCoefficient, if_pos hx] using he

end AxiomaticGW.SurfaceGenusTwo
