/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOnePivot
public import AxiomaticGW.Surfaces.GenusZeroMarkings

/-!
# Point markings and elliptic singleton coefficients

In genus at most one, a primary class-zero component is nonzero only at its
minimal stable arity: three in genus zero or one in genus one. An added
marking kills such a constant. The original ordered marking placements in an
elliptic singleton can therefore be accounted for by shifting its positive
elliptic vertex, retaining all original signed contractions and multiplicities.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne

open SurfacePolynomialReduction
open SurfaceLowGenus (pointVariable)
open SurfaceGenusZero (pointLabels)

/-- The class-zero vertex is the existing cubic or elliptic divisor constant. -/
theorem primary_constant_coefficient {X : SurfaceTarget} (q : SurfaceAncestorKey X)
    (hg : q.genus ≤ 1) (hp : q.IsPrimary) (hbeta : q.beta = 0) :
    RationalTerms.coefficient (primaryTerms q) 0 =
      if q.DimensionCompatible then
        if q.genus = 0 then SurfacePrimary.classicalValue q.primaryLabels
        else SurfacePrimary.genusOneZeroValue q.primaryLabels
      else 0 := by
  by_cases hzero : q.genus = 0
  · simpa only [hzero, ite_true] using
      SurfaceGenusZero.primary_constant_coefficient q hzero hp hbeta
  · have hone : q.genus = 1 := by omega
    by_cases hd : q.DimensionCompatible
    · simp only [primaryTerms, reduceVariable, if_pos hd, hbeta, ne_eq,
        not_true_eq_false, and_false, ite_false, degreeZeroValue?, hp, and_self,
        ite_true, hone, Nat.one_ne_zero, one_mul, RationalTerms.coefficient_term]
    · simp only [primaryTerms, reduceVariable, if_neg hd, RationalTerms.coefficient_zero]

/-- A new marking exceeds the arity of any nonzero primary class-zero vertex. -/
theorem constantCoefficient_fundamental_addMarking {X : SurfaceTarget}
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (hg : g ≤ 1)
    (a : Option S → SurfaceBasisLabel X) :
    constantCoefficient (GluingExpression.fundamental g (Option S) h.option) a = 0 := by
  let q := SurfaceAncestorKey.ofLabels g (Option S) h.option (0 : X.Curve) 0 a
  have hp : q.IsPrimary := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
    rfl
  change RationalTerms.coefficient (primaryTerms q) 0 = 0
  rw [primary_constant_coefficient q hg hp rfl]
  have hcard : q.primaryLabels.card = Fintype.card S + 1 := by
    simp only [q, SurfaceAncestorKey.primaryLabels, SurfaceAncestorKey.ofLabels,
      Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_option]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hg with hg | hg
  · have hn : q.primaryLabels.card ≠ 3 := by
      unfold StableArity at h
      rw [hg] at h
      omega
    simp only [show q.genus = 0 from hg, ite_true,
      SurfacePrimary.classicalValue, if_neg hn, ite_self]
  · have hn : q.primaryLabels.card ≠ 1 := by
      unfold StableArity at h
      rw [hg] at h
      omega
    have hqg : q.genus ≠ 0 := by change g ≠ 0; omega
    simp only [if_neg hqg, SurfacePrimary.genusOneZeroValue, if_neg hn, ite_self]

/-- At class zero the separating contraction has only the zero pair. -/
theorem constantCoefficient_separating {X : SurfaceTarget} {g h : ℕ} {S T : Type}
    [Fintype S] [Fintype T] (x : GluingExpression g (Option S))
    (y : GluingExpression h (Option T)) (a : S ⊕ T → SurfaceBasisLabel X) :
    constantCoefficient (x.separating y) a =
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (constantCoefficient x (Option.elim · b (a ∘ Sum.inl)) *
          constantCoefficient y (Option.elim · b.dual (a ∘ Sum.inr))) := by
  have hleft : PsiClasses.separatingLeftPowers (0 : S ⊕ T → ℕ) = 0 := by
    funext s
    cases s <;> rfl
  have hright : PsiClasses.separatingRightPowers (0 : S ⊕ T → ℕ) = 0 := by
    funext s
    cases s <;> rfl
  unfold constantCoefficient
  rw [GluingExpression.surfaceTerms, hleft, hright, X.splittings_eq,
    X.effective.splittings_zero, Finset.sum_singleton, RationalTerms.coefficient_sum]
  simp only [RationalTerms.coefficient_scale, RationalTerms.coefficient_mul_zero]

/-- Self-gluing retains the same two state flags in the constant contribution. -/
theorem constantCoefficient_nonseparating {X : SurfaceTarget} {g : ℕ} {S : Type}
    [Fintype S] (x : GluingExpression g (Option (Option S))) (a : S → SurfaceBasisLabel X) :
    constantCoefficient x.nonseparating a =
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        constantCoefficient x (Option.elim · b (fun t ↦ Option.elim t b.dual a)) := by
  have hk : PsiClasses.nonseparatingPowers (0 : S → ℕ) = 0 := by
    funext s
    rcases s with _ | (_ | s) <;> rfl
  simp only [constantCoefficient, GluingExpression.surfaceTerms, hk,
    RationalTerms.coefficient_sum, RationalTerms.coefficient_scale]

/-- Every separate placement of a new marking kills the class-zero constant.
Both elliptic vertices and rational loops are included. -/
theorem constantCoefficient_addMarking_eq_zero {X : SurfaceTarget}
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g ≤ 1)
    (z : GluingExpression g (Option S)) (hz : z ∈ x.addMarking)
    (a : Option S → SurfaceBasisLabel X) : constantCoefficient z a = 0 := by
  induction x with
  | fundamental g S h =>
    simp only [GluingExpression.addMarking, List.mem_singleton] at hz
    subst z
    exact constantCoefficient_fundamental_addMarking g S h hg a
  | relabel e x ih =>
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact ih hg w hw (a ∘ e.optionCongr)
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      rw [constantCoefficient_relabel, constantCoefficient_separating]
      apply Finset.sum_eq_zero
      intro b _
      rw [constantCoefficient_relabel, ihx (by omega) w hw, zero_mul, mul_zero]
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      rw [constantCoefficient_relabel, constantCoefficient_separating]
      apply Finset.sum_eq_zero
      intro b _
      rw [constantCoefficient_relabel, ihy (by omega) w hw, mul_zero, mul_zero]
  | nonseparating x ih =>
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    rw [constantCoefficient_nonseparating]
    apply Finset.sum_eq_zero
    intro b _
    rw [constantCoefficient_relabel, ih (by omega) w hw, mul_zero]

/-- An elliptic positive vertex with `n` additional points has this net
codimension shift; point factors do not change the divisor product. -/
def pointVertexCoefficient (X : SurfaceTarget) (beta : X.Curve) (n : ℕ)
    {S : Type} [Fintype S] (a : S → SurfaceBasisLabel X) : ℚ :=
  if ((∑ s, (a s).codimension : ℕ) : ℤ) + (n : ℤ) =
      X.c1Degree beta + (Fintype.card S : ℤ) then
    ∏ s, (a s).primaryFactor beta
  else 0

/-- At zero additional points this is the original elliptic vertex formula. -/
theorem pointVertexCoefficient_zero {X : SurfaceTarget} (beta : X.Curve)
    (S : Type) [Fintype S] (h : StableArity 1 S) (a : S → SurfaceBasisLabel X) :
    pointVertexCoefficient X beta 0 a =
      if (SurfaceAncestorKey.ofLabels 1 S h beta 0 a).DimensionCompatible then
        (SurfaceAncestorKey.ofLabels 1 S h beta 0 a).primaryCoefficient else 0 := by
  simp only [pointVertexCoefficient, SurfaceAncestorKey.DimensionCompatible,
    SurfaceAncestorKey.totalCodimension, SurfaceAncestorKey.primaryCoefficient,
    SurfaceAncestorKey.primaryLabels, SurfaceAncestorKey.ofLabels, Multiset.map_map,
    Function.comp_def, Pi.zero_apply, add_zero, Nat.cast_zero, Nat.cast_one,
    add_sub_cancel_right, Multiset.card_map, Finset.card_val, Finset.card_univ]
  rfl

/-- One new point adds one to the net dimension shift. -/
theorem pointVertexCoefficient_addPoint {X : SurfaceTarget} (beta : X.Curve) (n : ℕ)
    {S : Type} [Fintype S] (a : S → SurfaceBasisLabel X) :
    pointVertexCoefficient X beta n (Option.elim · .point a) =
      pointVertexCoefficient X beta (n + 1) a := by
  simp only [pointVertexCoefficient, Fintype.sum_option, Fintype.prod_option,
    Option.elim_none, Option.elim_some, SurfaceBasisLabel.codimension,
    SurfaceBasisLabel.primaryFactor, one_mul, Fintype.card_option,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  split_ifs <;> first | rfl | omega

/-- Shift only the positive elliptic vertex. Every class-zero factor retains
its full original graph and all of its labels. -/
def shiftedPointCoefficient (X : SurfaceTarget) (beta : X.Curve) (n : ℕ) :
    {g : ℕ} → {S : Type} → [Fintype S] →
      (x : GluingExpression g S) → g ≤ 1 → (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @GluingExpression.fundamental g _ _ _, _, a =>
      if g = 1 then pointVertexCoefficient X beta n a else 0
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, hg, a =>
      shiftedPointCoefficient X beta n x hg (a ∘ e)
  | _, _, _, @GluingExpression.separating _ _ _ _ _ _ x y, hg, a =>
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (constantCoefficient x (Option.elim · b (a ∘ Sum.inl)) *
          shiftedPointCoefficient X beta n y (by omega) (Option.elim · b.dual (a ∘ Sum.inr)) +
        shiftedPointCoefficient X beta n x (by omega) (Option.elim · b (a ∘ Sum.inl)) *
          constantCoefficient y (Option.elim · b.dual (a ∘ Sum.inr)))
  | _, _, _, @GluingExpression.nonseparating _ _ _ _, _, _ => 0

/-- Without a shift this is the exact extreme-splitting evaluator. -/
theorem shiftedPointCoefficient_zero {X : SurfaceTarget} (beta : X.Curve)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g ≤ 1)
    (a : S → SurfaceBasisLabel X) :
    shiftedPointCoefficient X beta 0 x hg a = pointCoefficientEval X beta x hg a := by
  induction x with
  | fundamental g S h =>
    by_cases hone : g = 1
    · subst g
      simpa only [shiftedPointCoefficient, pointCoefficientEval, ite_true] using
        pointVertexCoefficient_zero beta S h a
    · simp only [shiftedPointCoefficient, pointCoefficientEval, if_neg hone]
  | relabel e x ih => exact ih hg (a ∘ e)
  | separating x y ihx ihy =>
    simp only [shiftedPointCoefficient, pointCoefficientEval, ihx, ihy]
  | nonseparating x ih => rfl

private theorem list_sum_finset {α ι : Type*} [Fintype ι]
    (l : List α) (f : α → ι → ℚ) :
    (l.map (fun x ↦ ∑ i, f x i)).sum = ∑ i, (l.map (fun x ↦ f x i)).sum :=
  Multiset.sum_map_sum (m := (l : Multiset α))

/-- Summing the original one-marking placements shifts only the positive
elliptic vertex. Every placement on a class-zero component vanishes. -/
theorem sum_shiftedPointCoefficient_addMarking {X : SurfaceTarget}
    (beta : X.Curve) (n : ℕ) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g ≤ 1) (a : S → SurfaceBasisLabel X) :
    ((x.addMarking.map fun z ↦
      shiftedPointCoefficient X beta n z hg (Option.elim · .point a))).sum =
      shiftedPointCoefficient X beta (n + 1) x hg a := by
  induction x with
  | fundamental g S h =>
    simp only [GluingExpression.addMarking, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, shiftedPointCoefficient,
      pointVertexCoefficient_addPoint]
  | relabel e x ih =>
    simp only [GluingExpression.addMarking, List.map_map]
    change ((x.addMarking.map fun z ↦ shiftedPointCoefficient X beta n z hg
      ((Option.elim · .point a) ∘ e.optionCongr))).sum =
        shiftedPointCoefficient X beta (n + 1) x hg (a ∘ e)
    have he : (Option.elim · SurfaceBasisLabel.point a) ∘ e.optionCongr =
        (Option.elim · .point (a ∘ e)) := by
      funext t
      cases t <;> rfl
    rw [he]
    exact ih hg (a ∘ e)
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    have hg₁ : g₁ ≤ 1 := by omega
    have hg₂ : g₂ ≤ 1 := by omega
    have hlx (b : SurfaceBasisLabel X) :
        (Option.elim · b (((Option.elim · .point a) ∘ (optionSumEquivLeft S T).symm) ∘
          Sum.inl)) ∘ swapDoubleOption S =
        (Option.elim · .point (Option.elim · b (a ∘ Sum.inl))) := by
      funext t
      rcases t with _ | (_ | s) <;> rfl
    have hly (b : SurfaceBasisLabel X) :
        (Option.elim · b (((Option.elim · .point a) ∘ (optionSumEquivLeft S T).symm) ∘
          Sum.inr)) = (Option.elim · b (a ∘ Sum.inr)) := by
      funext t
      cases t <;> rfl
    have hrx (b : SurfaceBasisLabel X) :
        (Option.elim · b (((Option.elim · .point a) ∘ (optionSumEquivRight S T).symm) ∘
          Sum.inl)) = (Option.elim · b (a ∘ Sum.inl)) := by
      funext t
      cases t <;> rfl
    have hry (b : SurfaceBasisLabel X) :
        (Option.elim · b (((Option.elim · .point a) ∘ (optionSumEquivRight S T).symm) ∘
          Sum.inr)) ∘ swapDoubleOption T =
        (Option.elim · .point (Option.elim · b (a ∘ Sum.inr))) := by
      funext t
      rcases t with _ | (_ | s) <;> rfl
    have hl (w : GluingExpression g₁ (Option (Option S))) (hw : w ∈ x.addMarking) :
        shiftedPointCoefficient X beta n
          (((w.relabel (swapDoubleOption S)).separating y).relabel
            (optionSumEquivLeft S T).symm) hg (Option.elim · .point a) =
        ∑ b : SurfaceBasisLabel X, b.inverseWeight *
          (shiftedPointCoefficient X beta n w hg₁
              (Option.elim · .point (Option.elim · b (a ∘ Sum.inl))) *
            constantCoefficient y (Option.elim · b.dual (a ∘ Sum.inr))) := by
      simp only [shiftedPointCoefficient, constantCoefficient_relabel,
        constantCoefficient_addMarking_eq_zero x hg₁ w hw, zero_mul, zero_add, hlx, hly]
    have hr (w : GluingExpression g₂ (Option (Option T))) (hw : w ∈ y.addMarking) :
        shiftedPointCoefficient X beta n
          ((x.separating (w.relabel (swapDoubleOption T))).relabel
            (optionSumEquivRight S T).symm) hg (Option.elim · .point a) =
        ∑ b : SurfaceBasisLabel X, b.inverseWeight *
          (constantCoefficient x (Option.elim · b (a ∘ Sum.inl)) *
            shiftedPointCoefficient X beta n w hg₂
              (Option.elim · .point (Option.elim · b.dual (a ∘ Sum.inr)))) := by
      simp only [shiftedPointCoefficient, constantCoefficient_relabel,
        constantCoefficient_addMarking_eq_zero y hg₂ w hw, mul_zero, add_zero, hrx, hry]
    simp only [GluingExpression.addMarking, List.map_append, List.sum_append,
      List.map_map, Function.comp_def]
    rw [List.map_congr_left hl, List.map_congr_left hr, list_sum_finset, list_sum_finset]
    simp only [List.sum_map_mul_left, List.sum_map_mul_right, ihx, ihy,
      shiftedPointCoefficient, mul_add, Finset.sum_add_distrib]
    exact add_comm _ _
  | nonseparating x ih =>
    simp only [GluingExpression.addMarking, List.map_map, Function.comp_def,
      shiftedPointCoefficient]
    apply List.sum_eq_zero
    intro c hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
    rfl

/-- All ordered point placements are retained by induction on the original
forgetful expansion; only the elliptic vertex needs a dimension shift. -/
theorem sum_shiftedPointCoefficient_addMarkings {X : SurfaceTarget}
    (beta : X.Curve) (n m : ℕ) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g ≤ 1) (a : S → SurfaceBasisLabel X) :
    ((x.addMarkings n).map fun z ↦
      shiftedPointCoefficient X beta m z hg (pointLabels a n)).sum =
      shiftedPointCoefficient X beta (m + n) x hg a := by
  induction n generalizing m with
  | zero =>
    simp only [GluingExpression.addMarkings, pointLabels, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
  | succ n ih =>
    rw [GluingExpression.addMarkings, List.map_flatMap, List.flatMap_def, List.sum_flatten]
    simp only [List.map_map, Function.comp_def, pointLabels,
      sum_shiftedPointCoefficient_addMarking]
    rw [ih]
    congr 1
    omega

/-- The shifted computation equals the singleton coefficient of the complete
original marking expansion at every positive full class. -/
theorem sum_pointCoefficient_addMarkings {X : SurfaceTarget}
    (beta : X.Curve) (hbeta : beta ≠ 0) (n : ℕ) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g ≤ 1) (a : S → SurfaceBasisLabel X) :
    ((x.addMarkings n).map fun z ↦ RationalTerms.coefficient
      (z.surfaceTerms X (primaryVertexTerms X) beta 0 (pointLabels a n))
        {pointVariable X 1 beta}).sum = shiftedPointCoefficient X beta n x hg a := by
  simpa only [shiftedPointCoefficient_zero, pointCoefficientEval_eq beta hbeta,
    pointCoefficient, zero_add] using sum_shiftedPointCoefficient_addMarkings beta n 0 x hg a

end AxiomaticGW.SurfaceGenusOne

namespace AxiomaticGW.GetzlerGraphs

/-- Compute the marked elliptic singleton on the original 33 columns without
expanding the marking placements or positive full-class splittings. -/
def pointMarkedCoefficient (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) : ℚ :=
  ∑ i, requested i * SurfaceGenusOne.shiftedPointCoefficient X beta n (expression i) (by omega) a

/-- The fixed-size computation is the exact coefficient in the full original request. -/
theorem pointMarkedCoefficient_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (hbeta : beta ≠ 0) (a : Fin 4 → SurfaceBasisLabel X) :
    pointMarkedCoefficient X n beta a =
      RationalTerms.coefficient
        (primaryTerms X n beta 0 (SurfaceGenusZero.pointLabels a n))
        {SurfaceLowGenus.pointVariable X 1 beta} := by
  simp only [pointMarkedCoefficient, primaryTerms, surfaceTerms, RationalTerms.coefficient_sum,
    RationalTerms.coefficient_scale, RationalTerms.coefficient_list_sum, List.map_map,
    Function.comp_def]
  apply Finset.sum_congr rfl
  intro i _
  rw [SurfaceGenusOne.sum_pointCoefficient_addMarkings beta hbeta n (expression i) (by omega) a]

end AxiomaticGW.GetzlerGraphs
