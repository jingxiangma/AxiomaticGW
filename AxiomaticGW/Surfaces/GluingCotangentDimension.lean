/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GluingDegree

/-!
# Cotangent dimension vanishing in graph contractions

If every terminal component vanishes above its stable-curve dimension,
so does the full contraction above the sum of those dimensions. Each edge
lowers that sum by one, including a nonseparating edge. The natural-number
inequality below is exactly `sum(k) > 3*g - 3 + n - edgeCount`, with the
subtractions interpreted in integers. Full curve splittings and metric
weights remain in the original evaluator.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

/-- Above the sum of component dimensions, at least one factor in every
contraction vanishes. Only terminal genera bounded by the graph genus are needed. -/
theorem surfaceEval_zero_of_cotangent_bound {A : Type*} [CommRing A] [Algebra ℚ A]
    (X : SurfaceTarget) (v : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X)
    (hv : ∀ g' S' [Fintype S'] (h' : StableArity g' S') beta' k' a',
      g' ≤ g → 3 * g' + Fintype.card S' ≤ (∑ s, k' s) + 2 →
      v g' S' h' beta' k' a' = 0)
    (hd : 3 * g + Fintype.card S ≤ (∑ s, k s) + x.graph.graph.edgeCount + 2) :
    x.surfaceEval X v beta k a = 0 := by
  induction x generalizing beta with
  | fundamental g S h =>
      apply hv g S h beta k a le_rfl
      change 3 * g + Fintype.card S ≤ (∑ s, k s) + 0 + 2 at hd
      simpa only [Nat.add_zero] using hd
  | relabel e x ih =>
      apply ih beta (k ∘ e) (a ∘ e) hv
      rw [show (∑ s, (k ∘ e) s) = ∑ t, k t from e.sum_comp k, Fintype.card_congr e]
      exact hd
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
      change 3 * (g₁ + g₂) + Fintype.card (S ⊕ T) ≤
        (∑ s, k s) + (x.graph.graph.edgeCount + y.graph.graph.edgeCount + 1) + 2 at hd
      have hsum := PsiClasses.sum_separatingPowers k
      simp only [Fintype.card_sum] at hd
      have hsplit :
          3 * g₁ + Fintype.card (Option S) ≤
            (∑ s, PsiClasses.separatingLeftPowers k s) + x.graph.graph.edgeCount + 2 ∨
          3 * g₂ + Fintype.card (Option T) ≤
            (∑ t, PsiClasses.separatingRightPowers k t) + y.graph.graph.edgeCount + 2 := by
        simp only [Fintype.card_option]
        omega
      simp only [surfaceEval]
      apply Finset.sum_eq_zero
      intro split _
      apply Finset.sum_eq_zero
      intro b _
      rcases hsplit with hx | hy
      · rw [ihx split.1 _ _ (fun g' S' _ h' beta' k' a' hg hk ↦
          hv g' S' h' beta' k' a' (by omega) hk) hx]
        simp only [zero_mul, mul_zero]
      · rw [ihy split.2 _ _ (fun g' S' _ h' beta' k' a' hg hk ↦
          hv g' S' h' beta' k' a' (by omega) hk) hy]
        simp only [mul_zero]
  | @nonseparating g S _ x ih =>
      change 3 * (g + 1) + Fintype.card S ≤
        (∑ s, k s) + (x.graph.graph.edgeCount + 1) + 2 at hd
      simp only [surfaceEval]
      apply Finset.sum_eq_zero
      intro b _
      rw [ih beta _ _ (fun g' S' _ h' beta' k' a' hg hk ↦
        hv g' S' h' beta' k' a' (by omega) hk) (by
          simp only [Fintype.card_option, PsiClasses.sum_nonseparatingPowers]
          omega)]
      exact mul_zero _
end AxiomaticGW.GluingExpression

