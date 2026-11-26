/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroSupport

/-!
# Singleton coefficients in primary genus-zero equations

Homogeneity in the full effective curve class eliminates every strictly
positive split from the coefficient of the original point query. The remaining
two terms contract a degree-zero component against a component of the original
class, with the original signed inverse metric. This is an exact coefficient
identity, not an assumption that the coefficient is nonzero.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

open SurfacePolynomialReduction

/-- The complete singleton coefficient of a positive primary component is its
signed divisor product, subject to the existing dimension check. -/
theorem primary_point_coefficient {X : SurfaceTarget} (q : SurfaceAncestorKey X)
    (hg : q.genus = 0) (hp : q.IsPrimary) (hbeta : q.beta ≠ 0) :
    RationalTerms.coefficient (primaryTerms q) {pointVariable X q.beta} =
      if q.DimensionCompatible then q.primaryCoefficient else 0 := by
  by_cases hd : q.DimensionCompatible
  · rw [if_pos hd]
    by_cases hc : q.primaryCoefficient = 0
    · simp only [primaryTerms, reduceVariable, if_pos hd, if_pos (And.intro hp hbeta),
        hc, ite_true, RationalTerms.coefficient_zero]
    · have hq : q.pointQuery = SurfaceQuery.points X 0 q.beta
          (X.effective.energy q.beta - 1) := by
        rw [SurfaceAncestorKey.pointQuery, hg,
          q.point_count_of_genus_zero hg hp hd hc]
      simp only [primaryTerms, reduceVariable, if_pos hd, if_pos (And.intro hp hbeta),
        if_neg hc, degreeZeroValue?, hq, RationalTerms.coefficient_term,
        pointVariable, ite_true]
  · simp only [primaryTerms, reduceVariable, if_neg hd, RationalTerms.coefficient_zero]

/-- A degree-zero primary component contributes the dimension-checked classical cubic. -/
theorem primary_constant_coefficient {X : SurfaceTarget} (q : SurfaceAncestorKey X)
    (hg : q.genus = 0) (hp : q.IsPrimary) (hbeta : q.beta = 0) :
    RationalTerms.coefficient (primaryTerms q) 0 =
      if q.DimensionCompatible then SurfacePrimary.classicalValue q.primaryLabels else 0 := by
  by_cases hd : q.DimensionCompatible
  · simp only [primaryTerms, reduceVariable, if_pos hd, hbeta, ne_eq,
      not_true_eq_false, and_false, ite_false, degreeZeroValue?, hp, and_self,
      ite_true, hg, one_mul, RationalTerms.coefficient_term]
  · simp only [primaryTerms, reduceVariable, if_neg hd, RationalTerms.coefficient_zero]

/-- A monomial of a different full class has zero collected coefficient. -/
theorem PointTerms.coefficient_eq_zero_of_curve_ne {X : SurfaceTarget}
    {beta : X.Curve} {p : RationalTerms (Variable X)} (hp : PointTerms beta p)
    (m : Multiset (Variable X)) (hne : (m.map variableCurve).sum ≠ beta) :
    RationalTerms.coefficient p m = 0 := by
  unfold RationalTerms.coefficient
  have hmap : p.map (fun t ↦ if t.2 = m then t.1 else 0) = p.map (fun _ ↦ (0 : ℚ)) := by
    apply Multiset.map_congr rfl
    intro t ht
    apply if_neg
    intro he
    exact hne (he ▸ (hp t ht).2)
  rw [hmap, Multiset.sum_map_zero]

/-- Positive-class terms have no constant part, even before coefficients are collected. -/
theorem PointTerms.constant_eq_zero {X : SurfaceTarget} {beta : X.Curve}
    {p : RationalTerms (Variable X)} (hp : PointTerms beta p) (hbeta : beta ≠ 0) :
    RationalTerms.coefficient p 0 = 0 :=
  hp.coefficient_eq_zero_of_curve_ne 0 (Ne.symm hbeta)

/-- The coefficient of the dimension-compatible point query in a genus-zero graph. -/
def pointCoefficient {X : SurfaceTarget} {S : Type} [Fintype S]
    (x : GluingExpression 0 S) (beta : X.Curve) (a : S → SurfaceBasisLabel X) : ℚ :=
  RationalTerms.coefficient (x.surfaceTerms X (primaryVertexTerms X) beta 0 a)
    {pointVariable X beta}

/-- The constant contribution of a genus-zero graph at curve class zero. -/
def constantCoefficient {X : SurfaceTarget} {S : Type} [Fintype S]
    (x : GluingExpression 0 S) (a : S → SurfaceBasisLabel X) : ℚ :=
  RationalTerms.coefficient (x.surfaceTerms X (primaryVertexTerms X) 0 0 a) 0

/-- The elementary component formula retains signed divisor intersections. -/
theorem pointCoefficient_fundamental {X : SurfaceTarget} (S : Type) [Fintype S]
    (h : StableArity 0 S) (beta : X.Curve) (hbeta : beta ≠ 0)
    (a : S → SurfaceBasisLabel X) :
    pointCoefficient (GluingExpression.fundamental 0 S h) beta a =
      if (SurfaceAncestorKey.ofLabels 0 S h beta 0 a).DimensionCompatible then
        (SurfaceAncestorKey.ofLabels 0 S h beta 0 a).primaryCoefficient else 0 := by
  apply primary_point_coefficient _ rfl _ hbeta
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
  rfl

theorem constantCoefficient_fundamental {X : SurfaceTarget} (S : Type) [Fintype S]
    (h : StableArity 0 S) (a : S → SurfaceBasisLabel X) :
    constantCoefficient (GluingExpression.fundamental 0 S h) a =
      if (SurfaceAncestorKey.ofLabels 0 S h 0 0 a).DimensionCompatible then
        SurfacePrimary.classicalValue
          (SurfaceAncestorKey.ofLabels 0 S h 0 0 a).primaryLabels else 0 := by
  apply primary_constant_coefficient _ rfl _ rfl
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
  rfl

/-- A degree-zero primary component with any arity other than three vanishes.
Thus adding a point to a stable degree-zero vertex cannot contribute to the pivot. -/
theorem constantCoefficient_fundamental_eq_zero_of_card_ne_three {X : SurfaceTarget}
    (S : Type) [Fintype S] (h : StableArity 0 S) (a : S → SurfaceBasisLabel X)
    (hn : Fintype.card S ≠ 3) :
    constantCoefficient (GluingExpression.fundamental 0 S h) a = 0 := by
  rw [constantCoefficient_fundamental]
  have hc : (SurfaceAncestorKey.ofLabels 0 S h 0 0 a).primaryLabels.card ≠ 3 := by
    simpa only [SurfaceAncestorKey.primaryLabels, SurfaceAncestorKey.ofLabels,
      Multiset.card_map, Finset.card_val, Finset.card_univ] using hn
  simp only [SurfacePrimary.classicalValue, if_neg hc, ite_self]

theorem pointCoefficient_relabel {X : SurfaceTarget} {S T : Type} [Fintype S] [Fintype T]
    (x : GluingExpression 0 S) (e : S ≃ T) (beta : X.Curve)
    (a : T → SurfaceBasisLabel X) :
    pointCoefficient (x.relabel e) beta a = pointCoefficient x beta (a ∘ e) := rfl

theorem constantCoefficient_relabel {X : SurfaceTarget} {S T : Type} [Fintype S] [Fintype T]
    (x : GluingExpression 0 S) (e : S ≃ T) (a : T → SurfaceBasisLabel X) :
    constantCoefficient (x.relabel e) a = constantCoefficient x (a ∘ e) := rfl

/-- Only the two extreme curve-class splits contribute to a separating singleton.
This holds at every nonzero effective class and for arbitrarily many markings. -/
theorem pointCoefficient_separating {X : SurfaceTarget} {S T : Type}
    [Fintype S] [Fintype T] (x : GluingExpression 0 (Option S))
    (y : GluingExpression 0 (Option T)) (beta : X.Curve) (hbeta : beta ≠ 0)
    (a : S ⊕ T → SurfaceBasisLabel X) :
    pointCoefficient (x.separating y) beta a =
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (constantCoefficient x (Option.elim · b (a ∘ Sum.inl)) *
            pointCoefficient y beta (Option.elim · b.dual (a ∘ Sum.inr)) +
          pointCoefficient x beta (Option.elim · b (a ∘ Sum.inl)) *
            constantCoefficient y (Option.elim · b.dual (a ∘ Sum.inr))) := by
  have hleft : PsiClasses.separatingLeftPowers (0 : S ⊕ T → ℕ) = 0 := by
    funext s
    cases s <;> rfl
  have hright : PsiClasses.separatingRightPowers (0 : S ⊕ T → ℕ) = 0 := by
    funext s
    cases s <;> rfl
  have hzleft : (0, beta) ∈ X.splittings beta := by
    rw [X.splittings_eq, X.effective.mem_splittings, zero_add]
  have hzright : (beta, 0) ∈ X.splittings beta := by
    rw [X.splittings_eq, X.effective.mem_splittings, add_zero]
  have hne : (0, beta) ≠ (beta, 0) := by
    intro he
    exact hbeta (congrArg Prod.snd he)
  unfold pointCoefficient
  rw [GluingExpression.surfaceTerms, hleft, hright, RationalTerms.coefficient_sum]
  rw [Finset.sum_eq_add (0, beta) (beta, 0) hne]
  · simp only [RationalTerms.coefficient_sum, RationalTerms.coefficient_scale,
      RationalTerms.coefficient_mul_singleton]
    have hx (b : SurfaceBasisLabel X) :
        RationalTerms.coefficient
          (x.surfaceTerms X (primaryVertexTerms X) beta 0
            (Option.elim · b (a ∘ Sum.inl))) 0 = 0 :=
      (pointTerms_surface x rfl beta _).constant_eq_zero hbeta
    have hy (b : SurfaceBasisLabel X) :
        RationalTerms.coefficient
          (y.surfaceTerms X (primaryVertexTerms X) beta 0
            (Option.elim · b.dual (a ∘ Sum.inr))) 0 = 0 :=
      (pointTerms_surface y rfl beta _).constant_eq_zero hbeta
    simp only [hx, hy, mul_zero, zero_mul, add_zero, zero_add,
      constantCoefficient, ← Finset.sum_add_distrib, ← mul_add]
  · intro pair hpair hn
    have hsum : pair.1 + pair.2 = beta := by
      rw [X.splittings_eq] at hpair
      exact (X.effective.mem_splittings _ _ _).mp hpair
    have hp : pair.1 ≠ 0 := by
      intro he
      apply hn.1
      apply Prod.ext he
      simpa only [he, zero_add] using hsum
    have hq : pair.2 ≠ 0 := by
      intro he
      apply hn.2
      apply Prod.ext _ he
      simpa only [he, add_zero] using hsum
    rw [RationalTerms.coefficient_sum]
    apply Finset.sum_eq_zero
    intro b _
    rw [RationalTerms.coefficient_scale, RationalTerms.coefficient_mul_singleton,
      (pointTerms_surface x rfl pair.1 _).constant_eq_zero hp,
      (pointTerms_surface y rfl pair.2 _).constant_eq_zero hq,
      zero_mul, mul_zero, add_zero, mul_zero]
  · exact fun hn ↦ (hn hzleft).elim
  · exact fun hn ↦ (hn hzright).elim

/-- If extra markings land on both original WDVV vertices, neither can supply
the degree-zero cubic, so this placement contributes no leading coefficient. -/
theorem pointCoefficient_separating_fundamental_eq_zero {X : SurfaceTarget}
    (S T : Type) [Fintype S] [Fintype T]
    (hS : StableArity 0 (Option S)) (hT : StableArity 0 (Option T))
    (hcardS : Fintype.card (Option S) ≠ 3) (hcardT : Fintype.card (Option T) ≠ 3)
    (beta : X.Curve) (hbeta : beta ≠ 0) (a : S ⊕ T → SurfaceBasisLabel X) :
    pointCoefficient ((GluingExpression.fundamental 0 (Option S) hS).separating
      (GluingExpression.fundamental 0 (Option T) hT)) beta a = 0 := by
  rw [pointCoefficient_separating _ _ beta hbeta]
  apply Finset.sum_eq_zero
  intro b _
  rw [constantCoefficient_fundamental_eq_zero_of_card_ne_three _ _ _ hcardS,
    constantCoefficient_fundamental_eq_zero_of_card_ne_three _ _ _ hcardT,
    zero_mul, mul_zero, add_zero, mul_zero]

/-- Compute the singleton coefficient using only the two extreme splits.
The zero-class contractions retain the existing evaluator; the positive class
is never enumerated into all its effective splittings. Correctness requires
`beta ≠ 0`, as stated by `pointCoefficientEval_eq`.

The explicit genus proof excludes nonseparating expressions rather than giving
them a surrogate value. Additional-marking placements are still enumerated by
the original graph interface; no symmetric-placement optimization is asserted. -/
def pointCoefficientEval (X : SurfaceTarget) (beta : X.Curve) :
    {g : ℕ} → {S : Type} → [Fintype S] →
      (x : GluingExpression g S) → g = 0 → (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @GluingExpression.fundamental g S _ h, _, a =>
      let q := SurfaceAncestorKey.ofLabels g S h beta 0 a
      if q.DimensionCompatible then q.primaryCoefficient else 0
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, hg, a =>
      pointCoefficientEval X beta x hg (a ∘ e)
  | _, _, _, @GluingExpression.separating _ _ _ _ _ _ x y, hg, a =>
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (RationalTerms.coefficient
            (x.surfaceTerms X (primaryVertexTerms X) 0 0 (Option.elim · b (a ∘ Sum.inl))) 0 *
          pointCoefficientEval X beta y (Nat.eq_zero_of_add_eq_zero_left hg)
            (Option.elim · b.dual (a ∘ Sum.inr)) +
          pointCoefficientEval X beta x (Nat.eq_zero_of_add_eq_zero_right hg)
            (Option.elim · b (a ∘ Sum.inl)) *
          RationalTerms.coefficient
            (y.surfaceTerms X (primaryVertexTerms X) 0 0
              (Option.elim · b.dual (a ∘ Sum.inr))) 0)
  | _, _, _, @GluingExpression.nonseparating _ _ _ _, hg, _ =>
      False.elim (Nat.succ_ne_zero _ hg)

/-- The optimized coefficient is exactly that of the complete original expansion,
at every positive class, with no energy or marking bound. -/
theorem pointCoefficientEval_eq {X : SurfaceTarget} (beta : X.Curve) (hbeta : beta ≠ 0)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g = 0)
    (a : S → SurfaceBasisLabel X) :
    pointCoefficientEval X beta x hg a =
      RationalTerms.coefficient (x.surfaceTerms X (primaryVertexTerms X) beta 0 a)
        {pointVariable X beta} := by
  induction x with
  | fundamental g S h =>
    apply (primary_point_coefficient (SurfaceAncestorKey.ofLabels g S h beta 0 a)
      hg _ hbeta).symm
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
    rfl
  | relabel e x ih => exact ih hg (a ∘ e)
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    have hg₁ := Nat.eq_zero_of_add_eq_zero_right hg
    have hg₂ := Nat.eq_zero_of_add_eq_zero_left hg
    subst g₁
    subst g₂
    change _ = pointCoefficient (x.separating y) beta a
    rw [pointCoefficient_separating _ _ beta hbeta]
    simp only [pointCoefficientEval, ihx, ihy, constantCoefficient, pointCoefficient]
  | nonseparating x ih => omega

end AxiomaticGW.SurfaceGenusZero

namespace AxiomaticGW.WDVV

/-- Exact singleton coefficient through the verified extreme-split evaluator.
The request, original channel weights and marking multiplicities are unchanged. -/
def primaryPointCoefficient (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) : ℚ :=
  ∑ i, requested i *
    ((((expression i).addMarkings n).map fun z ↦
      SurfaceGenusZero.pointCoefficientEval X beta z rfl a).sum)

/-- The quicker computation certifies the leading coefficient of the held WDVV request. -/
theorem primaryPointCoefficient_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (hbeta : beta ≠ 0) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    primaryPointCoefficient X n beta a =
      RationalTerms.coefficient (primaryTerms X n beta 0 a)
        {SurfaceGenusZero.pointVariable X beta} := by
  simp only [primaryPointCoefficient, primaryTerms, RationalTerms.coefficient_sum,
    RationalTerms.coefficient_scale, RationalTerms.coefficient_list_sum, List.map_map,
    Function.comp_def, SurfaceGenusZero.pointCoefficientEval_eq beta hbeta]

end AxiomaticGW.WDVV
