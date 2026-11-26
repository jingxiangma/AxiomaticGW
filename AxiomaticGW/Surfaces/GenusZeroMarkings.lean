/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroPivot

/-!
# Point markings and the leading genus-zero coefficient

A primary degree-zero vertex contributes only at arity three. Any added
marking on such a vertex therefore kills its constant contribution. This
controls the original ordered marking placements without identifying distinct
graphs or discarding their multiplicities.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

open SurfacePolynomialReduction

/-- At total class zero the only effective splitting is the zero pair. -/
theorem constantCoefficient_separating {X : SurfaceTarget} {S T : Type}
    [Fintype S] [Fintype T] (x : GluingExpression 0 (Option S))
    (y : GluingExpression 0 (Option T)) (a : S ⊕ T → SurfaceBasisLabel X) :
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
  have hsplit : X.splittings 0 = {(0, 0)} := by
    ext pair
    rw [X.splittings_eq, X.effective.mem_splittings, Finset.mem_singleton]
    constructor
    · intro h
      apply Prod.ext <;> funext i
      · exact Nat.eq_zero_of_add_eq_zero_right (congrFun h i)
      · exact Nat.eq_zero_of_add_eq_zero_left (congrFun h i)
    · rintro rfl
      exact zero_add _
  unfold constantCoefficient
  rw [GluingExpression.surfaceTerms, hleft, hright, hsplit,
    Finset.sum_singleton, RationalTerms.coefficient_sum]
  simp only [RationalTerms.coefficient_scale, RationalTerms.coefficient_mul_zero]

/-- A new marking on any degree-zero primary tree makes its constant part zero.
The assertion holds separately for every placement and every state label. -/
theorem constantCoefficient_addMarking_eq_zero {X : SurfaceTarget}
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g = 0)
    (z : GluingExpression g (Option S)) (hz : z ∈ x.addMarking)
    (a : Option S → SurfaceBasisLabel X) :
    RationalTerms.coefficient (z.surfaceTerms X (primaryVertexTerms X) 0 0 a) 0 = 0 := by
  induction x with
  | fundamental g S h =>
    simp only [GluingExpression.addMarking, List.mem_singleton] at hz
    subst z
    subst g
    apply constantCoefficient_fundamental_eq_zero_of_card_ne_three
    have hs : 3 ≤ Fintype.card S := by
      simpa only [StableArity, mul_zero, zero_add] using h
    rw [Fintype.card_option]
    omega
  | relabel e x ih =>
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact ih hg w hw (a ∘ e.optionCongr)
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    have hg₁ := Nat.eq_zero_of_add_eq_zero_right hg
    have hg₂ := Nat.eq_zero_of_add_eq_zero_left hg
    subst g₁
    subst g₂
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      change constantCoefficient _ _ = 0
      rw [constantCoefficient_relabel, constantCoefficient_separating]
      apply Finset.sum_eq_zero
      intro b _
      rw [constantCoefficient_relabel]
      change _ * (RationalTerms.coefficient
        (w.surfaceTerms X (primaryVertexTerms X) 0 0 _) 0 * _) = 0
      rw [ihx rfl w hw, zero_mul, mul_zero]
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      change constantCoefficient _ _ = 0
      rw [constantCoefficient_relabel, constantCoefficient_separating]
      apply Finset.sum_eq_zero
      intro b _
      rw [constantCoefficient_relabel]
      change _ * (_ * RationalTerms.coefficient
        (w.surfaceTerms X (primaryVertexTerms X) 0 0 _) 0) = 0
      rw [ihy rfl w hw, mul_zero, mul_zero]
  | nonseparating x ih => omega

/-- A positive component after adjoining `n` point insertions. Each point adds
two to codimension and one to virtual dimension, giving the displayed net shift.
Its divisor product is unchanged since a point has primary factor one. -/
def pointVertexCoefficient (X : SurfaceTarget) (beta : X.Curve) (n : ℕ)
    {S : Type} [Fintype S] (a : S → SurfaceBasisLabel X) : ℚ :=
  if ((∑ s, (a s).codimension : ℕ) : ℤ) + (n : ℤ) =
      X.c1Degree beta - 1 + (Fintype.card S : ℤ) then
    ∏ s, (a s).primaryFactor beta
  else 0

/-- At zero added points this is the existing primary vertex formula. -/
theorem pointVertexCoefficient_zero {X : SurfaceTarget} (beta : X.Curve)
    (S : Type) [Fintype S] (h : StableArity 0 S) (a : S → SurfaceBasisLabel X) :
    pointVertexCoefficient X beta 0 a =
      if (SurfaceAncestorKey.ofLabels 0 S h beta 0 a).DimensionCompatible then
        (SurfaceAncestorKey.ofLabels 0 S h beta 0 a).primaryCoefficient else 0 := by
  simp only [pointVertexCoefficient, SurfaceAncestorKey.DimensionCompatible,
    SurfaceAncestorKey.totalCodimension, SurfaceAncestorKey.primaryCoefficient,
    SurfaceAncestorKey.primaryLabels, SurfaceAncestorKey.ofLabels, Multiset.map_map,
    Function.comp_def, Pi.zero_apply, add_zero, Nat.cast_zero, Multiset.card_map,
    Finset.card_val, Finset.card_univ]
  rfl

/-- Adding one more point gives exactly one further dimension shift. -/
theorem pointVertexCoefficient_addPoint {X : SurfaceTarget} (beta : X.Curve) (n : ℕ)
    {S : Type} [Fintype S] (a : S → SurfaceBasisLabel X) :
    pointVertexCoefficient X beta n (Option.elim · .point a) =
      pointVertexCoefficient X beta (n + 1) a := by
  simp only [pointVertexCoefficient, Fintype.sum_option, Fintype.prod_option,
    Option.elim_none, Option.elim_some, SurfaceBasisLabel.codimension,
    SurfaceBasisLabel.primaryFactor, one_mul, Fintype.card_option,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  split_ifs <;> first | rfl | omega

/-- Shift the positive-class vertex in each linear contribution by `n` extra
points. Constant components retain all their original flags and labels. -/
def shiftedPointCoefficient (X : SurfaceTarget) (beta : X.Curve) (n : ℕ) :
    {g : ℕ} → {S : Type} → [Fintype S] →
      (x : GluingExpression g S) → g = 0 → (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @GluingExpression.fundamental _ _ _ _, _, a =>
      pointVertexCoefficient X beta n a
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, hg, a =>
      shiftedPointCoefficient X beta n x hg (a ∘ e)
  | _, _, _, @GluingExpression.separating _ _ _ _ _ _ x y, hg, a =>
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (RationalTerms.coefficient
            (x.surfaceTerms X (primaryVertexTerms X) 0 0 (Option.elim · b (a ∘ Sum.inl))) 0 *
          shiftedPointCoefficient X beta n y (Nat.eq_zero_of_add_eq_zero_left hg)
            (Option.elim · b.dual (a ∘ Sum.inr)) +
          shiftedPointCoefficient X beta n x (Nat.eq_zero_of_add_eq_zero_right hg)
            (Option.elim · b (a ∘ Sum.inl)) *
          RationalTerms.coefficient
            (y.surfaceTerms X (primaryVertexTerms X) 0 0
              (Option.elim · b.dual (a ∘ Sum.inr))) 0)
  | _, _, _, @GluingExpression.nonseparating _ _ _ _, hg, _ =>
      False.elim (Nat.succ_ne_zero _ hg)

/-- The unshifted computation is the previously certified coefficient evaluator. -/
theorem shiftedPointCoefficient_zero {X : SurfaceTarget} (beta : X.Curve)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g = 0)
    (a : S → SurfaceBasisLabel X) :
    shiftedPointCoefficient X beta 0 x hg a = pointCoefficientEval X beta x hg a := by
  induction x with
  | fundamental g S h =>
    subst g
    exact pointVertexCoefficient_zero beta S h a
  | relabel e x ih => exact ih hg (a ∘ e)
  | separating x y ihx ihy =>
    simp only [shiftedPointCoefficient, pointCoefficientEval, ihx, ihy]
  | nonseparating x ih => omega

private theorem list_sum_finset {α ι : Type*} [Fintype ι]
    (l : List α) (f : α → ι → ℚ) :
    (l.map (fun x ↦ ∑ i, f x i)).sum = ∑ i, (l.map (fun x ↦ f x i)).sum :=
  Multiset.sum_map_sum (m := (l : Multiset α))

/-- Summing the original one-marking placements shifts only the positive
component. Every degree-zero placement vanishes by the preceding theorem. -/
theorem sum_shiftedPointCoefficient_addMarking {X : SurfaceTarget}
    (beta : X.Curve) (n : ℕ) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g = 0) (a : S → SurfaceBasisLabel X) :
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
    have hg₁ := Nat.eq_zero_of_add_eq_zero_right hg
    have hg₂ := Nat.eq_zero_of_add_eq_zero_left hg
    subst g₁
    subst g₂
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
    have hkS : (0 : Option (Option S) → ℕ) ∘ swapDoubleOption S = 0 := rfl
    have hkT : (0 : Option (Option T) → ℕ) ∘ swapDoubleOption T = 0 := rfl
    have hl (w : GluingExpression 0 (Option (Option S))) (hw : w ∈ x.addMarking) :
        shiftedPointCoefficient X beta n
          (((w.relabel (swapDoubleOption S)).separating y).relabel
            (optionSumEquivLeft S T).symm) rfl (Option.elim · .point a) =
        ∑ b : SurfaceBasisLabel X, b.inverseWeight *
          (shiftedPointCoefficient X beta n w rfl
              (Option.elim · .point (Option.elim · b (a ∘ Sum.inl))) *
            RationalTerms.coefficient
              (y.surfaceTerms X (primaryVertexTerms X) 0 0
                (Option.elim · b.dual (a ∘ Sum.inr))) 0) := by
      simp only [shiftedPointCoefficient, GluingExpression.surfaceTerms, hkS,
        constantCoefficient_addMarking_eq_zero x rfl w hw, zero_mul, zero_add, hlx, hly]
    have hr (w : GluingExpression 0 (Option (Option T))) (hw : w ∈ y.addMarking) :
        shiftedPointCoefficient X beta n
          ((x.separating (w.relabel (swapDoubleOption T))).relabel
            (optionSumEquivRight S T).symm) rfl (Option.elim · .point a) =
        ∑ b : SurfaceBasisLabel X, b.inverseWeight *
          (RationalTerms.coefficient
              (x.surfaceTerms X (primaryVertexTerms X) 0 0
                (Option.elim · b (a ∘ Sum.inl))) 0 *
            shiftedPointCoefficient X beta n w rfl
              (Option.elim · .point (Option.elim · b.dual (a ∘ Sum.inr)))) := by
      simp only [shiftedPointCoefficient, GluingExpression.surfaceTerms, hkT,
        constantCoefficient_addMarking_eq_zero y rfl w hw, mul_zero, add_zero, hrx, hry]
    simp only [GluingExpression.addMarking, List.map_append, List.sum_append,
      List.map_map, Function.comp_def]
    rw [List.map_congr_left hl, List.map_congr_left hr, list_sum_finset, list_sum_finset]
    simp only [List.sum_map_mul_left, List.sum_map_mul_right, ihx, ihy,
      shiftedPointCoefficient, mul_add, Finset.sum_add_distrib]
    exact add_comm _ _
  | nonseparating x ih => omega

/-- Retain the original states and give every added marking the point class. -/
def pointLabels {X : SurfaceTarget} {S : Type} (a : S → SurfaceBasisLabel X) :
    (n : ℕ) → ExtraMarkings n S → SurfaceBasisLabel X
  | 0 => a
  | n + 1 => (Option.elim · .point (pointLabels a n))

/-- Every ordered marking placement is accounted for, without enumerating it.
The sole surviving placement for each positive component carries all the points. -/
theorem sum_shiftedPointCoefficient_addMarkings {X : SurfaceTarget}
    (beta : X.Curve) (n m : ℕ) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g = 0) (a : S → SurfaceBasisLabel X) :
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

/-- The complete marked leading coefficient is computed on the original tree
with a dimension shift, preserving every original placement multiplicity. -/
theorem sum_pointCoefficient_addMarkings {X : SurfaceTarget}
    (beta : X.Curve) (hbeta : beta ≠ 0) (n : ℕ) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g = 0) (a : S → SurfaceBasisLabel X) :
    ((x.addMarkings n).map fun z ↦ RationalTerms.coefficient
      (z.surfaceTerms X (primaryVertexTerms X) beta 0 (pointLabels a n))
        {pointVariable X beta}).sum = shiftedPointCoefficient X beta n x hg a := by
  simpa only [shiftedPointCoefficient_zero, pointCoefficientEval_eq beta hbeta, zero_add]
    using sum_shiftedPointCoefficient_addMarkings beta n 0 x hg a

end AxiomaticGW.SurfaceGenusZero

namespace AxiomaticGW.WDVV

/-- Compute the point-marked coefficient on the original three graphs, with
no expansion of the `2^n` marking placements or positive-class splittings. -/
def pointMarkedCoefficient (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) : ℚ :=
  ∑ i, requested i * SurfaceGenusZero.shiftedPointCoefficient X beta n (expression i) rfl a

/-- The fixed-size computation is exactly the coefficient of the original marked request. -/
theorem pointMarkedCoefficient_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (hbeta : beta ≠ 0) (a : Fin 4 → SurfaceBasisLabel X) :
    pointMarkedCoefficient X n beta a =
      RationalTerms.coefficient
        (primaryTerms X n beta 0 (SurfaceGenusZero.pointLabels a n))
        {SurfaceGenusZero.pointVariable X beta} := by
  simp only [pointMarkedCoefficient, primaryTerms, RationalTerms.coefficient_sum,
    RationalTerms.coefficient_scale, RationalTerms.coefficient_list_sum, List.map_map,
    Function.comp_def, SurfaceGenusZero.sum_pointCoefficient_addMarkings beta hbeta]

end AxiomaticGW.WDVV
