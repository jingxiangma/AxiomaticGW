/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.CurveSum
public import AxiomaticGW.Surfaces.ScalarPointContraction
public import AxiomaticGW.Tautological.DecoratedGluingMarkingBounds
public import AxiomaticGW.Surfaces.LowGenusVirtualDimension
public import AxiomaticGW.Surfaces.PrimaryPointPullback

/-! # The virtual dimension of a decorated graph with added point insertions

The codimension of the entire glued stratum determines the only possible
number of additional labelled points. At a separating node the codimension
of its right subtree also determines the distribution, including the binomial
weight. The resulting evaluator applies to point pullbacks of any surface
vertex satisfying the ordinary virtual-dimension condition.
-/

@[expose] public section
namespace AxiomaticGW.GluingExpression
variable {X : SurfaceTarget}

/-- Codimension of a glued cotangent decoration, computed in the given gluing tree. -/
def gluedCotangentDegree : {g : ℕ} → {S : Type} → [Fintype S] →
    (x : GluingExpression g S) → x.CotangentDecoration → ℕ
  | _, _, _, @fundamental _ S _ _, d => ∑ s : S, d s
  | _, _, _, @relabel _ _ _ _ _ _ x, d => x.gluedCotangentDegree d
  | _, _, _, @separating _ _ _ _ _ _ x y, d =>
    x.gluedCotangentDegree d.1 + y.gluedCotangentDegree d.2 + 1
  | _, _, _, @nonseparating _ _ _ x, d => x.gluedCotangentDegree d + 1

/-- The tree-degree computation agrees with total decorated stratum codimension. -/
theorem gluedCotangentDegree_eq {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) :
    x.gluedCotangentDegree d = (x.decoratedGraph d).codimension := by
  induction x with
  | fundamental => simp only [gluedCotangentDegree, decoratedGraph,
      DecoratedStableGraph.oneVertex_codimension, Finsupp.sum_zero_index, zero_add]
  | relabel e x ih => simp only [gluedCotangentDegree, decoratedGraph,
      DecoratedStableGraph.relabel_codimension, ih]
  | separating x y ihx ihy => simp only [gluedCotangentDegree, decoratedGraph,
      DecoratedStableGraph.separating_codimension, ihx, ihy]
  | nonseparating x ih => simp only [gluedCotangentDegree, decoratedGraph,
      DecoratedStableGraph.nonseparating_codimension, ih]

/-- The virtual dimension forces this signed number of additional labelled point insertions. -/
def cotangentPointDemand {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (b : X.Curve) (a : S → SurfaceBasisLabel X) : ℤ :=
  X.c1Degree b + (g : ℤ) - 1 + (Fintype.card S : ℤ) -
    (x.gluedCotangentDegree d : ℤ) - ((∑ s, (a s).codimension : ℕ) : ℤ)

private theorem demand_relabel {g : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (e : S ≃ T) (x : GluingExpression g S) (d : x.CotangentDecoration) (b : X.Curve)
    (a : T → SurfaceBasisLabel X) :
    (x.relabel e).cotangentPointDemand d b a = x.cotangentPointDemand d b (a ∘ e) := by
  have hs := e.sum_comp (fun t ↦ (a t).codimension)
  simp only [Function.comp_def] at hs ⊢
  unfold cotangentPointDemand
  rw [hs, Fintype.card_congr e]
  rfl

private theorem demand_sum {g₁ g₂ : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (x : GluingExpression g₁ (Option S)) (y : GluingExpression g₂ (Option T))
    (d : x.CotangentDecoration × y.CotangentDecoration) (left right : X.Curve)
    (a : S ⊕ T → SurfaceBasisLabel X) (b : SurfaceBasisLabel X) :
    x.cotangentPointDemand d.1 left (Option.elim · b (a ∘ Sum.inl)) +
      y.cotangentPointDemand d.2 right (Option.elim · b.dual (a ∘ Sum.inr)) =
      (x.separating y).cotangentPointDemand d (left + right) a := by
  have hb : b.codimension + b.dual.codimension = 2 := by cases b <;> rfl
  simp only [cotangentPointDemand, gluedCotangentDegree, Fintype.sum_option, Fintype.sum_sum_type,
    Fintype.card_option, Fintype.card_sum, Option.elim_none, Option.elim_some,
    Function.comp_def, Nat.cast_add, Nat.cast_one, map_add]
  omega

private theorem demand_loop {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g (Option (Option S))) (d : x.CotangentDecoration)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) (b : SurfaceBasisLabel X) :
    x.cotangentPointDemand d beta (Option.elim · b (fun t ↦ Option.elim t b.dual a)) =
    x.nonseparating.cotangentPointDemand d beta a := by
  have hb : b.codimension + b.dual.codimension = 2 := by cases b <;> rfl
  simp only [cotangentPointDemand, gluedCotangentDegree, Fintype.sum_option, Fintype.card_option,
    Option.elim_none, Option.elim_some, Nat.cast_add, Nat.cast_one]
  omega

/-- Dimension support of an individual stable vertex with additional labelled points. -/
def VertexPointDimension (v : ℕ → SurfaceCotangentVertexValues X ℚ) : Prop :=
  ∀ (n g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (d : S → ℕ) (l : DecidableEq S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X),
    (n : ℤ) ≠ (GluingExpression.fundamental g S h).cotangentPointDemand d beta a →
      v n g S h d l beta a = 0

/-- Dimension support of every stable vertex implies dimension support of a glued class. -/
theorem scalarPointContraction_zero_of_demand {v : ℕ → SurfaceCotangentVertexValues X ℚ}
    (hv : VertexPointDimension v) {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) (hn : (n : ℤ) ≠ x.cotangentPointDemand d beta a) :
    x.scalarPointContraction X v d l beta n a = 0 := by
  induction x generalizing beta n with
  | fundamental g S h => exact hv n g S h d l beta a hn
  | relabel e x ih => exact ih d l beta n (a ∘ e) (by rwa [demand_relabel] at hn)
  | separating x y ihx ihy =>
    unfold scalarPointContraction
    apply Finset.sum_eq_zero
    intro split hs
    have hb := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
    apply Finset.sum_eq_zero
    intro b _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro p hp
    apply mul_eq_zero_of_right
    have h := demand_sum x y d split.1 split.2 a b
    rw [hb] at h
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    by_cases hr : (p.2 : ℤ) =
        y.cotangentPointDemand d.2 split.2 (Option.elim · b.dual (a ∘ Sum.inr))
    · have hl : (p.1 : ℤ) ≠ x.cotangentPointDemand d.1 split.1 (Option.elim · b (a ∘ Sum.inl)) := by
        omega
      rw [ihx d.1 l.1 split.1 p.1 _ hl]
      simp only [zero_mul, ite_self]
    · rw [ihy d.2 l.2 split.2 p.2 _ hr, if_pos rfl]
  | nonseparating x ih =>
    unfold scalarPointContraction
    apply Finset.sum_eq_zero
    intro b _
    rw [ih d l beta n _ (by rwa [demand_loop]), mul_zero]

/-- A raw labelled vertex respects the usual virtual dimension. -/
def GradedVertex (v : SurfaceVertexValues X ℚ) : Prop :=
  ∀ g (S : Type) [Fintype S] (h : StableArity g S) beta k a,
    SurfaceLowGenusPointCache.virtualDefect g beta k a ≠ 0 → v g S h beta k a = 0

/-- Adding a labelled point by the original cotangent pullback preserves virtual dimension,
including every rational-tail correction. -/
theorem pointPullback_dimension {v : SurfaceVertexValues X ℚ} (hv : GradedVertex v) :
    VertexPointDimension (SurfacePointPullback.vertex X v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro g S _ h d l beta a hn
    cases n with
    | zero =>
      rw [SurfacePointPullback.vertex]
      apply hv
      unfold cotangentPointDemand gluedCotangentDegree at hn
      unfold SurfaceLowGenusPointCache.virtualDefect
      omega
    | succ n =>
      rw [SurfacePointPullback.vertex]
      apply Multiset.sum_eq_zero
      intro w hw
      obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hw
      rw [← scalarPointContraction_eq]
      apply mul_eq_zero_of_right
      apply scalarPointContraction_zero_of_demand
      · intro m gm T _ ht k e b labels hd
        by_cases hm : m ≤ n
        · simpa only [dif_pos hm] using ih m (by omega) gm T ht k e b labels hd
        · simp only [dif_neg hm]
      · have hc := (addCotangentMarking_bounds (.fundamental g S h) d l s hs).1
        rw [← gluedCotangentDegree_eq, ← gluedCotangentDegree_eq] at hc
        unfold cotangentPointDemand at hn ⊢
        simp only [hc, Fintype.card_option, Fintype.sum_option, Option.elim_none, Option.elim_some,
          Nat.cast_add, Nat.cast_one,
          show (SurfaceBasisLabel.point : SurfaceBasisLabel X).codimension
            = 2 from rfl, Nat.cast_ofNat] at hn ⊢
        omega

/-- Evaluate the single grading-compatible distribution and its labelled binomial weight. -/
def selectedPointProduct (left right : ℕ → ℚ) (n : ℕ) (k : ℤ) : ℚ :=
  if 0 ≤ k ∧ k ≤ (n : ℤ) then
    let r := right k.toNat
    if r = 0 then 0 else (n.choose k.toNat : ℚ) * (left (n - k.toNat) * r)
  else 0

private theorem selectedPointProduct_eq (f r : ℕ → ℚ) (n : ℕ) (k : ℤ)
    (hr : ∀ t : ℕ, (t : ℤ) ≠ k → r t = 0) :
    selectedPointProduct f r n k =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose p.1 : ℚ) *
        (if r p.2 = 0 then 0 else f p.1 * r p.2) := by
  have skip (a b : ℚ) : (if b = 0 then 0 else a * b) = a * b := by
    split_ifs with h
    · rw [h, mul_zero]
    · rfl
  simp only [skip]
  by_cases hk : 0 ≤ k ∧ k ≤ (n : ℤ)
  · rw [selectedPointProduct, if_pos hk,
      SurfacePointPullback.sum_binomial_of_right_support f r n k.toNat
        (fun j hj ↦ hr j (by omega))]
    by_cases hz : r k.toNat = 0
    · rw [if_pos hz, hz, mul_zero, mul_zero]
    · exact if_neg hz
  · rw [selectedPointProduct, if_neg hk]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [hr p.2 (by omega), mul_zero, mul_zero]

/-- At each separating node, the decorated right subtree determines the point distribution. -/
def dimensionPointContraction (X : SurfaceTarget) (v : ℕ → SurfaceCotangentVertexValues X ℚ) :
    {g : ℕ} → {S : Type} → [Fintype S] → (x : GluingExpression g S) →
    x.CotangentDecoration → x.DecidableLabels → X.Curve → ℕ → (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @fundamental g S _ h, d, l, beta, n, a => v n g S h d l beta a
  | _, _, _, @relabel _ _ _ _ _ e x, d, l, beta, n, a =>
    dimensionPointContraction X v x d l beta n (a ∘ e)
  | _, _, _, @separating _ _ _ _ _ _ x y, d, l, beta, n, a =>
    if (n : ℤ) ≠ (x.separating y).cotangentPointDemand d beta a then 0 else
    X.sumSubcurves beta fun c ↦ ∑ b : SurfaceBasisLabel X, b.inverseWeight *
      selectedPointProduct
        (fun m ↦ dimensionPointContraction X v x d.1 l.1 c m (Option.elim · b (a ∘ Sum.inl)))
        (fun m ↦ dimensionPointContraction X v y d.2 l.2 (beta - c) m
          (Option.elim · b.dual (a ∘ Sum.inr))) n
        (y.cotangentPointDemand d.2 (beta - c) (Option.elim · b.dual (a ∘ Sum.inr)))
  | _, _, _, @nonseparating _ _ _ x, d, l, beta, n, a =>
    ∑ b : SurfaceBasisLabel X, b.inverseWeight * dimensionPointContraction X v x d l beta n
      (Option.elim · b (fun t ↦ Option.elim t b.dual a))

/-- Dimension pruning preserves every ordinary decorated graph, including all point pullbacks. -/
theorem dimensionPointContraction_eq {v : ℕ → SurfaceCotangentVertexValues X ℚ}
    (hv : VertexPointDimension v) {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) :
    x.dimensionPointContraction X v d l beta n a = x.scalarPointContraction X v d l beta n a := by
  induction x generalizing beta n with
  | fundamental => rfl
  | relabel e x ih => exact ih d l beta n (a ∘ e)
  | separating x y ihx ihy =>
    by_cases hd : (n : ℤ) ≠ (x.separating y).cotangentPointDemand d beta a
    · rw [dimensionPointContraction, if_pos hd,
        scalarPointContraction_zero_of_demand hv _ _ _ _ _ _ hd]
    · simp only [dimensionPointContraction, if_neg hd, SurfaceTarget.sumSubcurves_eq,
        scalarPointContraction, SurfaceTarget.splittings, WeightedCurveClass.splittings, ihx, ihy]
      rw [Finset.sum_image (fun _ _ _ _ h ↦ congrArg Prod.fst h)]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      apply selectedPointProduct_eq
      intro j hj
      exact scalarPointContraction_zero_of_demand hv y d.2 l.2 (beta - c) j _ hj
  | nonseparating x ih => simp only [dimensionPointContraction, scalarPointContraction, ih]

end AxiomaticGW.GluingExpression
