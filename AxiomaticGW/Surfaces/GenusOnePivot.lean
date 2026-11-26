/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneSupport
public import AxiomaticGW.Surfaces.GenusZeroPivot

/-!
# Exact singleton coefficients in primary genus-one equations

Full-class homogeneity removes every strictly positive splitting from a
singleton coefficient. Genus support removes the elliptic singleton from
rational components and nonseparating graphs. The resulting evaluator uses
only the original extreme splittings and signed node contractions.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceLowGenus

open SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)

/-- A different full curve class cannot contribute to a collected coefficient. -/
theorem PointTerms.coefficient_eq_zero_of_curve_ne {X : SurfaceTarget} {g : ℕ}
    {beta : X.Curve} {p : RationalTerms (Variable X)} (hp : PointTerms g beta p)
    (m : Multiset (Variable X)) (hne : (m.map variableCurve).sum ≠ beta) :
    RationalTerms.coefficient p m = 0 := by
  unfold RationalTerms.coefficient
  have hmap : p.map (fun t ↦ if t.2 = m then t.1 else 0) = p.map (fun _ ↦ (0 : ℚ)) := by
    apply Multiset.map_congr rfl
    intro t ht
    apply if_neg
    intro he
    exact hne (he ▸ (hp t ht).2.1)
  rw [hmap, Multiset.sum_map_zero]

/-- A positive-class graph has no constant part. -/
theorem PointTerms.constant_eq_zero {X : SurfaceTarget} {g : ℕ} {beta : X.Curve}
    {p : RationalTerms (Variable X)} (hp : PointTerms g beta p) (hbeta : beta ≠ 0) :
    RationalTerms.coefficient p 0 = 0 :=
  hp.coefficient_eq_zero_of_curve_ne 0 (Ne.symm hbeta)

/-- A monomial with larger total component genus cannot occur in the graph. -/
theorem PointTerms.coefficient_eq_zero_of_genus_lt {X : SurfaceTarget} {g : ℕ}
    {beta : X.Curve} {p : RationalTerms (Variable X)} (hp : PointTerms g beta p)
    (m : Multiset (Variable X)) (hlt : g < (m.map variableGenus).sum) :
    RationalTerms.coefficient p m = 0 := by
  unfold RationalTerms.coefficient
  have hmap : p.map (fun t ↦ if t.2 = m then t.1 else 0) = p.map (fun _ ↦ (0 : ℚ)) := by
    apply Multiset.map_congr rfl
    intro t ht
    apply if_neg
    intro he
    have hle := (hp t ht).2.2
    rw [he] at hle
    omega
  rw [hmap, Multiset.sum_map_zero]

end SurfaceLowGenus

namespace SurfaceGenusOne

open SurfacePolynomialReduction SurfaceLowGenus

/-- Coefficient of the requested elliptic point singleton in the full graph expansion. -/
def pointCoefficient {X : SurfaceTarget} {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (beta : X.Curve) (a : S → SurfaceBasisLabel X) : ℚ :=
  RationalTerms.coefficient (x.surfaceTerms X (primaryVertexTerms X) beta 0 a)
    {pointVariable X 1 beta}

/-- The actual class-zero constant contribution, with its original genus retained. -/
def constantCoefficient {X : SurfaceTarget} {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (a : S → SurfaceBasisLabel X) : ℚ :=
  RationalTerms.coefficient (x.surfaceTerms X (primaryVertexTerms X) 0 0 a) 0

/-- A rational graph contains no genus-one variable, even at the same full class. -/
theorem pointCoefficient_genus_zero {X : SurfaceTarget} {S : Type} [Fintype S]
    (x : GluingExpression 0 S) (beta : X.Curve) (a : S → SurfaceBasisLabel X) :
    pointCoefficient x beta a = 0 :=
  (pointTerms_surface x (by omega) beta a).coefficient_eq_zero_of_genus_lt _ (by
    change (0 : ℕ) < 1
    omega)

/-- The elliptic vertex contributes its signed divisor product, subject to dimension. -/
theorem primary_point_coefficient {X : SurfaceTarget} (q : SurfaceAncestorKey X)
    (hg : q.genus ≤ 1) (hp : q.IsPrimary) (hbeta : q.beta ≠ 0) :
    RationalTerms.coefficient (primaryTerms q) {pointVariable X 1 q.beta} =
      if q.genus = 1 then if q.DimensionCompatible then q.primaryCoefficient else 0 else 0 := by
  by_cases hone : q.genus = 1
  · rw [if_pos hone]
    by_cases hd : q.DimensionCompatible
    · rw [if_pos hd]
      by_cases hc : q.primaryCoefficient = 0
      · simp only [primaryTerms, reduceVariable, if_pos hd, if_pos (And.intro hp hbeta),
          hc, ite_true, RationalTerms.coefficient_zero]
      · have hq : q.pointQuery = SurfaceQuery.points X 1 q.beta
            (X.effective.energy q.beta + 1 - 1) := by
          rw [SurfaceAncestorKey.pointQuery, q.point_count_of_primary hp hd hc, hone]
        simp only [primaryTerms, reduceVariable, if_pos hd, if_pos (And.intro hp hbeta),
          if_neg hc, degreeZeroValue?, hq, RationalTerms.coefficient_term,
          pointVariable, ite_true]
    · simp only [primaryTerms, reduceVariable, if_neg hd, RationalTerms.coefficient_zero]
  · rw [if_neg hone]
    exact (pointTerms_primary q hg hp).coefficient_eq_zero_of_genus_lt _ (by
      change q.genus < 1
      omega)

/-- The fundamental formula distinguishes rational and elliptic vertices explicitly. -/
theorem pointCoefficient_fundamental {X : SurfaceTarget} (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (hg : g ≤ 1) (beta : X.Curve) (hbeta : beta ≠ 0)
    (a : S → SurfaceBasisLabel X) :
    pointCoefficient (GluingExpression.fundamental g S h) beta a =
      if g = 1 then
        if (SurfaceAncestorKey.ofLabels g S h beta 0 a).DimensionCompatible then
          (SurfaceAncestorKey.ofLabels g S h beta 0 a).primaryCoefficient else 0
      else 0 := by
  apply primary_point_coefficient _ hg _ hbeta
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
  rfl

theorem pointCoefficient_relabel {X : SurfaceTarget} {g : ℕ} {S T : Type}
    [Fintype S] [Fintype T] (x : GluingExpression g S) (e : S ≃ T) (beta : X.Curve)
    (a : T → SurfaceBasisLabel X) :
    pointCoefficient (x.relabel e) beta a = pointCoefficient x beta (a ∘ e) := rfl

theorem constantCoefficient_relabel {X : SurfaceTarget} {g : ℕ} {S T : Type}
    [Fintype S] [Fintype T] (x : GluingExpression g S) (e : S ≃ T)
    (a : T → SurfaceBasisLabel X) :
    constantCoefficient (x.relabel e) a = constantCoefficient x (a ∘ e) := rfl

/-- Only the two extreme full-class splittings contribute to the elliptic singleton. -/
theorem pointCoefficient_separating {X : SurfaceTarget} {g h : ℕ} {S T : Type}
    [Fintype S] [Fintype T] (x : GluingExpression g (Option S))
    (y : GluingExpression h (Option T)) (hgenus : g + h ≤ 1)
    (beta : X.Curve) (hbeta : beta ≠ 0) (a : S ⊕ T → SurfaceBasisLabel X) :
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
      (pointTerms_surface x (by omega) beta _).constant_eq_zero hbeta
    have hy (b : SurfaceBasisLabel X) :
        RationalTerms.coefficient
          (y.surfaceTerms X (primaryVertexTerms X) beta 0
            (Option.elim · b.dual (a ∘ Sum.inr))) 0 = 0 :=
      (pointTerms_surface y (by omega) beta _).constant_eq_zero hbeta
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
      (pointTerms_surface x (by omega) pair.1 _).constant_eq_zero hp,
      (pointTerms_surface y (by omega) pair.2 _).constant_eq_zero hq,
      zero_mul, mul_zero, add_zero, mul_zero]
  · exact fun hn ↦ (hn hzleft).elim
  · exact fun hn ↦ (hn hzright).elim

/-- A nonseparating genus-one graph has only rational component variables. -/
theorem pointCoefficient_nonseparating {X : SurfaceTarget} {S : Type} [Fintype S]
    (x : GluingExpression 0 (Option (Option S))) (beta : X.Curve)
    (a : S → SurfaceBasisLabel X) : pointCoefficient x.nonseparating beta a = 0 := by
  have hk : PsiClasses.nonseparatingPowers (0 : S → ℕ) = 0 := by
    funext s
    rcases s with _ | (_ | s) <;> rfl
  simp only [pointCoefficient, GluingExpression.surfaceTerms, hk,
    RationalTerms.coefficient_sum, RationalTerms.coefficient_scale]
  change (∑ b : SurfaceBasisLabel X, b.inverseWeight * pointCoefficient x beta _) = 0
  simp only [pointCoefficient_genus_zero, mul_zero, Finset.sum_const_zero]

/-- Compute the exact elliptic singleton using only the extreme class splits.
The genus bound makes every nonseparating branch a proved rational contribution. -/
def pointCoefficientEval (X : SurfaceTarget) (beta : X.Curve) :
    {g : ℕ} → {S : Type} → [Fintype S] →
      (x : GluingExpression g S) → g ≤ 1 → (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @GluingExpression.fundamental g S _ h, _, a =>
      let q := SurfaceAncestorKey.ofLabels g S h beta 0 a
      if g = 1 then if q.DimensionCompatible then q.primaryCoefficient else 0 else 0
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, hg, a =>
      pointCoefficientEval X beta x hg (a ∘ e)
  | _, _, _, @GluingExpression.separating _ _ _ _ _ _ x y, hg, a =>
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (constantCoefficient x (Option.elim · b (a ∘ Sum.inl)) *
          pointCoefficientEval X beta y (by omega) (Option.elim · b.dual (a ∘ Sum.inr)) +
        pointCoefficientEval X beta x (by omega) (Option.elim · b (a ∘ Sum.inl)) *
          constantCoefficient y (Option.elim · b.dual (a ∘ Sum.inr)))
  | _, _, _, @GluingExpression.nonseparating _ _ _ _, _, _ => 0

/-- This coefficient evaluator agrees with the entire original expansion,
without a class bound, numerical seed, or nonvanishing assumption. -/
theorem pointCoefficientEval_eq {X : SurfaceTarget} (beta : X.Curve) (hbeta : beta ≠ 0)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g ≤ 1)
    (a : S → SurfaceBasisLabel X) :
    pointCoefficientEval X beta x hg a = pointCoefficient x beta a := by
  induction x with
  | fundamental g S h => exact (pointCoefficient_fundamental g S h hg beta hbeta a).symm
  | relabel e x ih => exact ih hg (a ∘ e)
  | separating x y ihx ihy =>
    rw [pointCoefficient_separating _ _ hg beta hbeta]
    simp only [pointCoefficientEval, ihx, ihy]
  | @nonseparating g S _ x ih =>
    have hz : g = 0 := by omega
    subst g
    exact (pointCoefficient_nonseparating x beta a).symm

end SurfaceGenusOne

end AxiomaticGW
