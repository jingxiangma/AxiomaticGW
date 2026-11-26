/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroExpansion

/-!
# Point-marking compression including nonseparating graphs

Separate component counts and binomial weights retain every ordered point
placement. Self-gluing transports its two node states past the new external
point and preserves the signed contraction. The construction covers the
Getzler loop graphs and agrees exactly with the existing genus-zero evaluator.
The equality proof is algebraic and valid at every graph genus; it adds no
higher-genus reduction rule or geometric hypothesis.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfacePointExpansion

open SurfacePolynomialReduction
open SurfaceGenusZero (pointLabels)

/-- The original primary terms with the added points counted at each vertex.
Only marking placements are compressed; class splits and node labels are unchanged. -/
def compactTerms (X : SurfaceTarget) :
    {g : ℕ} → {S : Type} → [Fintype S] →
      (x : GluingExpression g S) → X.Curve → ℕ →
        (S → SurfaceBasisLabel X) → RationalTerms (Variable X)
  | _, _, _, @GluingExpression.fundamental g S _ h, beta, n, a =>
      primaryTerms ((SurfaceAncestorKey.ofLabels g S h beta 0 a).addPoints n)
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, beta, n, a =>
      compactTerms X x beta n (a ∘ e)
  | _, _, _, @GluingExpression.separating _ _ _ _ _ _ x y, beta, n, a =>
      ∑ split ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
        RationalTerms.scale b.inverseWeight
          (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, RationalTerms.scale (n.choose ij.1)
            (RationalTerms.mul
              (compactTerms X x split.1 ij.1
                (Option.elim · b (a ∘ Sum.inl)))
              (compactTerms X y split.2 ij.2
                (Option.elim · b.dual (a ∘ Sum.inr)))))
  | _, _, _, @GluingExpression.nonseparating _ _ _ x, beta, n, a =>
      ∑ b : SurfaceBasisLabel X, RationalTerms.scale b.inverseWeight
        (compactTerms X x beta n (Option.elim · b (fun t ↦ Option.elim t b.dual a)))

variable {A : Type*} [CommRing A] [Algebra ℚ A]

omit [Algebra ℚ A] in
private theorem sum_list_finset {α ι : Type*} (l : List α) (s : Finset ι)
    (f : α → ι → A) :
    (l.map (fun x ↦ ∑ i ∈ s, f x i)).sum = ∑ i ∈ s, (l.map (fun x ↦ f x i)).sum :=
  Multiset.sum_map_sum (m := (l : Multiset α))

omit [Algebra ℚ A] in
private theorem binomial_succ (f g : ℕ → A) (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      (n.choose ij.1 : A) * (f (ij.1 + 1) * g ij.2)) +
      (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (n.choose ij.1 : A) * (f ij.1 * g (ij.2 + 1))) =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), ((n + 1).choose ij.1 : A) *
          (f ij.1 * g ij.2) := by
  rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j ↦ f i * g j) n]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← hsum, Nat.choose_symm_add]

/-- At zero added points the compressed expression is the original graph. -/
theorem eval_compactTerms_zero {X : SurfaceTarget} (v : Variable X → A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) :
    RationalTerms.eval v (compactTerms X x beta 0 a) =
      RationalTerms.eval v (x.surfaceTerms X (primaryVertexTerms X) beta 0 a) := by
  induction x generalizing beta with
  | fundamental g S h =>
    rw [compactTerms, SurfaceAncestorKey.addPoints_zero]
    rfl
  | relabel e x ih => exact ih beta (a ∘ e)
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    have hl : PsiClasses.separatingLeftPowers (0 : S ⊕ T → ℕ) = 0 := by
      funext s
      cases s <;> rfl
    have hr : PsiClasses.separatingRightPowers (0 : S ⊕ T → ℕ) = 0 := by
      funext s
      cases s <;> rfl
    simp only [compactTerms, GluingExpression.surfaceTerms, RationalTerms.eval_sum,
      RationalTerms.eval_scale, RationalTerms.eval_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, Nat.choose_zero_right, Nat.cast_one, map_one, one_mul,
      ihx, ihy, hl, hr]
  | @nonseparating g S _ x ih =>
    have hk : PsiClasses.nonseparatingPowers (0 : S → ℕ) = 0 := by
      funext s
      rcases s with _ | (_ | s) <;> rfl
    simp only [compactTerms, GluingExpression.surfaceTerms, RationalTerms.eval_sum,
      RationalTerms.eval_scale, hk, ih]

/-- Pascal's identity counts the two possible sides for the next labelled point. -/
theorem sum_eval_compactTerms_addMarking {X : SurfaceTarget} (v : Variable X → A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    ((x.addMarking.map fun z ↦ RationalTerms.eval v
      (compactTerms X z beta n (Option.elim · .point a)))).sum =
        RationalTerms.eval v (compactTerms X x beta (n + 1) a) := by
  induction x generalizing beta n with
  | fundamental g S h =>
    simp only [GluingExpression.addMarking, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, compactTerms]
    exact congrArg (fun q ↦ RationalTerms.eval v (primaryTerms q))
      (SurfaceAncestorKey.addPoints_ofLabels_option g S h beta a n)
  | relabel e x ih =>
    simp only [GluingExpression.addMarking, List.map_map, Function.comp_def, compactTerms]
    have he : (Option.elim · SurfaceBasisLabel.point a) ∘ e.optionCongr =
        (Option.elim · .point (a ∘ e)) := by
      funext t
      cases t <;> rfl
    change ((x.addMarking.map fun z ↦ RationalTerms.eval v
      (compactTerms X z beta n ((Option.elim · .point a) ∘ e.optionCongr)))).sum = _
    rw [he]
    exact ih beta n (a ∘ e)
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
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
    simp only [GluingExpression.addMarking, List.map_append, List.sum_append,
      List.map_map, Function.comp_def]
    simp only [compactTerms, hlx, hly, hrx, hry,
      RationalTerms.eval_sum, RationalTerms.eval_scale, RationalTerms.eval_mul, map_natCast]
    simp only [sum_list_finset, List.sum_map_mul_left, List.sum_map_mul_right, ihx, ihy]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro split _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [← mul_add]
    congr 1
    exact binomial_succ
      (fun k ↦ RationalTerms.eval v (compactTerms X x split.1 k
        (Option.elim · b (a ∘ Sum.inl))))
      (fun k ↦ RationalTerms.eval v (compactTerms X y split.2 k
        (Option.elim · b.dual (a ∘ Sum.inr)))) n
  | @nonseparating g S _ x ih =>
    have ha (b : SurfaceBasisLabel X) :
        (Option.elim · b (fun t ↦ Option.elim t b.dual (Option.elim · .point a))) ∘
          (forgetNonseparatingEquiv S).symm =
        (Option.elim · .point (Option.elim · b (fun t ↦ Option.elim t b.dual a))) := by
      funext s
      rcases s with _ | (_ | (_ | s)) <;> rfl
    simp only [Function.comp_def] at ha
    simp only [GluingExpression.addMarking, List.map_map, Function.comp_def,
      compactTerms, RationalTerms.eval_sum, RationalTerms.eval_scale]
    simp only [sum_list_finset, List.sum_map_mul_left, ha, ih]

/-- Equality to the complete ordered expansion, in every rational algebra. -/
theorem sum_eval_compactTerms_addMarkings {X : SurfaceTarget} (v : Variable X → A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (n m : ℕ) (a : S → SurfaceBasisLabel X) :
    ((x.addMarkings n).map fun z ↦ RationalTerms.eval v
      (compactTerms X z beta m (pointLabels a n))).sum =
        RationalTerms.eval v (compactTerms X x beta (m + n) a) := by
  induction n generalizing m with
  | zero =>
    simp only [GluingExpression.addMarkings, pointLabels, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
  | succ n ih =>
    rw [GluingExpression.addMarkings, List.map_flatMap, List.flatMap_def, List.sum_flatten]
    simp only [List.map_map, Function.comp_def, pointLabels, sum_eval_compactTerms_addMarking]
    rw [ih]
    congr 2
    omega

/-- Compression changes neither the polynomial nor any valuation of the original equation. -/
theorem eval_compactTerms {X : SurfaceTarget} (v : Variable X → A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    RationalTerms.eval v (compactTerms X x beta n a) =
      RationalTerms.eval v (((x.addMarkings n).map fun z ↦
        z.surfaceTerms X (primaryVertexTerms X) beta 0 (pointLabels a n)).sum) := by
  rw [RationalTerms.eval_list_sum]
  simp only [List.map_map, Function.comp_def]
  simpa only [eval_compactTerms_zero, zero_add] using
    (sum_eval_compactTerms_addMarkings v x beta n 0 a).symm

/-- The established genus-zero compression is preserved exactly, including term order. -/
theorem compactTerms_genus_zero (X : SurfaceTarget) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g = 0) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) :
    compactTerms X x beta n a = SurfaceGenusZero.compactTerms X x hg beta n a := by
  induction x generalizing beta n with
  | fundamental g S h => rfl
  | relabel e x ih => exact ih hg beta n (a ∘ e)
  | separating x y ihx ihy =>
    simp only [compactTerms, SurfaceGenusZero.compactTerms,
      ihx (Nat.eq_zero_of_add_eq_zero_right hg), ihy (Nat.eq_zero_of_add_eq_zero_left hg)]
  | nonseparating x ih => omega

end SurfacePointExpansion

namespace GetzlerGraphs

/-- The exact Getzler combination, with point placements compressed binomially. -/
def compactPrimaryTerms (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) :
    RationalTerms (SurfacePolynomialReduction.Variable X) :=
  ∑ i, RationalTerms.scale (requested i)
    (SurfacePointExpansion.compactTerms X (expression i) beta n a)

/-- Every valuation of the compressed Getzler expression equals the original request. -/
theorem eval_compactPrimaryTerms {A : Type*} [CommRing A] [Algebra ℚ A]
    {X : SurfaceTarget} (v : SurfacePolynomialReduction.Variable X → A)
    (n : ℕ) (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) :
    RationalTerms.eval v (compactPrimaryTerms X n beta a) =
      RationalTerms.eval v (primaryTerms X n beta 0 (SurfaceGenusZero.pointLabels a n)) := by
  simp only [compactPrimaryTerms, primaryTerms, surfaceTerms, RationalTerms.eval_sum,
    RationalTerms.eval_scale, SurfacePointExpansion.eval_compactTerms]

end GetzlerGraphs

end AxiomaticGW
