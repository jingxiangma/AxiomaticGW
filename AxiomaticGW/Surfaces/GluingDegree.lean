/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GluingEvaluation
public import Mathlib.Algebra.BigOperators.Option

/-!
# Cotangent-degree bounds for component evaluation

External powers restrict to the component carrying their marking. Node powers
are zero, so no component gains cotangent degree. Component genus is also at
most the total genus. These bounds justify recursive evaluation after one
external power has been lowered by a proved cotangent boundary equation.
-/

@[expose] public section

namespace AxiomaticGW
namespace PsiClasses

/-- Restriction distributes, but never creates, external cotangent powers. -/
theorem sum_separatingPowers {S T : Type} [Fintype S] [Fintype T] (k : S ⊕ T → ℕ) :
    (∑ s, separatingLeftPowers k s) + (∑ t, separatingRightPowers k t) = ∑ u, k u := by
  simp only [Fintype.sum_option, separatingLeftPowers, separatingRightPowers,
    zero_add, Fintype.sum_sum_type]

theorem sum_separatingLeftPowers_le {S T : Type} [Fintype S] [Fintype T]
    (k : S ⊕ T → ℕ) : (∑ s, separatingLeftPowers k s) ≤ ∑ u, k u := by
  rw [← sum_separatingPowers k]
  exact Nat.le_add_right _ _

theorem sum_separatingRightPowers_le {S T : Type} [Fintype S] [Fintype T]
    (k : S ⊕ T → ℕ) : (∑ t, separatingRightPowers k t) ≤ ∑ u, k u := by
  rw [← sum_separatingPowers k]
  exact Nat.le_add_left _ _

/-- A loop introduces two zero-power node markings. -/
theorem sum_nonseparatingPowers {S : Type} [Fintype S] (k : S → ℕ) :
    (∑ t, nonseparatingPowers k t) = ∑ s, k s := by
  simp only [Fintype.sum_option, nonseparatingPowers, zero_add]

end PsiClasses

namespace GluingExpression

/-- Every terminal dependency has bounded genus and cotangent degree. Thus
agreement only in that smaller domain suffices for agreement of the contraction. -/
theorem surfaceEval_congr_of_bounds {A : Type*} [CommRing A] [Algebra ℚ A]
    (X : SurfaceTarget) (v w : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X)
    (hv : ∀ g' S' [Fintype S'] (h' : StableArity g' S') beta' k' a',
      g' ≤ g → (∑ s, k' s) ≤ ∑ s, k s →
      v g' S' h' beta' k' a' = w g' S' h' beta' k' a') :
    x.surfaceEval X v beta k a = x.surfaceEval X w beta k a := by
  induction x generalizing beta with
  | fundamental g S h => exact hv g S h beta k a le_rfl le_rfl
  | relabel e x ih =>
      apply ih
      intro g' S' _ h' beta' k' a' hg hk
      apply hv g' S' h' beta' k' a' hg
      exact hk.trans_eq (e.sum_comp k)
  | separating x y ihx ihy =>
      simp only [surfaceEval]
      apply Finset.sum_congr rfl
      intro split _
      apply Finset.sum_congr rfl
      intro b _
      congr 2
      · apply ihx
        intro g' S' _ h' beta' k' a' hg hk
        exact hv g' S' h' beta' k' a' (by omega)
          (hk.trans (PsiClasses.sum_separatingLeftPowers_le k))
      · apply ihy
        intro g' S' _ h' beta' k' a' hg hk
        exact hv g' S' h' beta' k' a' (by omega)
          (hk.trans (PsiClasses.sum_separatingRightPowers_le k))
  | nonseparating x ih =>
      simp only [surfaceEval]
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      apply ih
      intro g' S' _ h' beta' k' a' hg hk
      exact hv g' S' h' beta' k' a' (by omega)
        (hk.trans_eq (PsiClasses.sum_nonseparatingPowers k))

end GluingExpression
end AxiomaticGW
