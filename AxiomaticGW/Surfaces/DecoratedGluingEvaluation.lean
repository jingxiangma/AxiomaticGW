/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedGluingEvaluation
public import AxiomaticGW.Surfaces.GluingEvaluation

/-!
# Executable surface contractions with node cotangent powers

The original inverse metric and every full curve-class splitting are retained.
Original component cotangent powers, including future node branches, are
added to pulled-back external powers. This extends the existing evaluator
without modifying it or imposing a new numerical axiom.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

/-- Explicit signed inverse-metric and full-class evaluation. -/
def surfaceDecoratedEval {A : Type*} [CommRing A] [Algebra ℚ A]
    (X : SurfaceTarget) (vertex : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → X.Curve → (S → ℕ) →
      (S → SurfaceBasisLabel X) → A
  | @fundamental g S _ h, d, beta, k, a => vertex g S h beta (k + d) a
  | @relabel _ _ _ _ _ e x, d, beta, k, a => x.surfaceDecoratedEval X vertex d beta (k ∘ e) (a ∘ e)
  | @separating _ _ _ _ _ _ x y, d, beta, k, a =>
      ∑ split ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
        algebraMap ℚ A b.inverseWeight *
          (x.surfaceDecoratedEval X vertex d.1 split.1 (PsiClasses.separatingLeftPowers k)
            (Option.elim · b (a ∘ Sum.inl)) *
           y.surfaceDecoratedEval X vertex d.2 split.2 (PsiClasses.separatingRightPowers k)
            (Option.elim · b.dual (a ∘ Sum.inr)))
  | @nonseparating _ _ _ x, d, beta, k, a =>
      ∑ b : SurfaceBasisLabel X, algebraMap ℚ A b.inverseWeight *
        x.surfaceDecoratedEval X vertex d beta (PsiClasses.nonseparatingPowers k)
          (Option.elim · b (fun t ↦ Option.elim t b.dual a))

/-- Polynomial substitution commutes with every finite graph operation. -/
theorem surfaceDecoratedEval_map {A B : Type*} [CommRing A] [Algebra ℚ A]
    [CommRing B] [Algebra ℚ B] (f : A →ₐ[ℚ] B)
    (X : SurfaceTarget) (vertex : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (d : x.CotangentDecoration)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    f (x.surfaceDecoratedEval X vertex d beta k a) =
      x.surfaceDecoratedEval X (fun g S _ h beta k a ↦ f (vertex g S h beta k a)) d beta k a := by
  induction x generalizing beta with
  | fundamental g S h => rfl
  | relabel e x ih => exact ih d beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    simp only [surfaceDecoratedEval, map_sum, map_mul, f.commutes, ihx, ihy]
  | nonseparating x ih =>
    simp only [surfaceDecoratedEval, map_sum, map_mul, f.commutes, ih]

/-- Zero component powers recover the existing evaluator at every external power. -/
theorem surfaceDecoratedEval_zeroDecoration {A : Type*} [CommRing A] [Algebra ℚ A]
    (X : SurfaceTarget) (vertex : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    x.surfaceDecoratedEval X vertex x.zeroDecoration beta k a =
      x.surfaceEval X vertex beta k a := by
  induction x generalizing beta with
  | fundamental g S h =>
    change vertex g S h beta (k + 0) a = vertex g S h beta k a
    rw [add_zero]
  | relabel e x ih => exact ih beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    simp only [surfaceDecoratedEval, zeroDecoration, surfaceEval, ihx, ihy]
  | nonseparating x ih =>
    simp only [surfaceDecoratedEval, zeroDecoration, surfaceEval, ih]

/-- Only the genera of the original components are consulted, even when cycles
raise the total genus or node decorations raise the cotangent powers. -/
theorem surfaceDecoratedEval_congr_of_genus {A : Type*} [CommRing A] [Algebra ℚ A]
    (X : SurfaceTarget) (v w : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X)
    (hv : ∀ g' S' [Fintype S'] (h' : StableArity g' S') beta' k' a',
      g' ≤ x.maxComponentGenus → v g' S' h' beta' k' a' = w g' S' h' beta' k' a') :
    x.surfaceDecoratedEval X v d beta k a = x.surfaceDecoratedEval X w d beta k a := by
  induction x generalizing beta with
  | fundamental g S h => exact hv g S h beta (k + d) a le_rfl
  | relabel e x ih => exact ih d beta (k ∘ e) (a ∘ e) hv
  | separating x y ihx ihy =>
    simp only [surfaceDecoratedEval]
    apply Finset.sum_congr rfl
    intro split _
    apply Finset.sum_congr rfl
    intro b _
    congr 2
    · apply ihx
      intro g' S' _ h' beta' k' a' hg
      exact hv g' S' h' beta' k' a' (hg.trans (le_max_left _ _))
    · apply ihy
      intro g' S' _ h' beta' k' a' hg
      exact hv g' S' h' beta' k' a' (hg.trans (le_max_right _ _))
  | nonseparating x ih =>
    simp only [surfaceDecoratedEval]
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    exact ih d beta _ _ hv

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}

/-- The executable edge expansion equals the existing geometric contraction.
Only identification of the supplied pairing with the surface pairing is needed. -/
theorem surfaceDecoratedEval_eq_gwDecoratedAncestorContraction
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (hp : Omega.pairing = (SurfaceCohomology.frobenius X.blowups).pairing)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (d : x.CotangentDecoration)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    x.surfaceDecoratedEval X (Omega.surfaceVertexValues P I) d beta k a =
      x.gwDecoratedAncestorContraction Omega P I d beta k (fun s ↦ (a s).value) := by
  induction x generalizing beta with
  | fundamental g S h => rfl
  | relabel e x ih =>
    exact ih d beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    simp only [surfaceDecoratedEval, gwDecoratedAncestorContraction, sum_apply, hp,
      SurfaceCohomology.pairContract_eq_sum, X.splittings_eq, Algebra.algebraMap_self_apply]
    apply Finset.sum_congr rfl
    intro split _
    apply Finset.sum_congr rfl
    intro b _
    rw [ihx d.1, ihy d.2]
    congr 2 <;> congr 1 <;> funext s <;> cases s <;> rfl
  | nonseparating x ih =>
    simp only [surfaceDecoratedEval, gwDecoratedAncestorContraction, hp,
      SurfaceCohomology.selfContract_eq_sum, MultilinearMap.domDomCongr_apply,
      Algebra.algebraMap_self_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [ih d]
    congr 2
    funext s
    rcases s with _ | (_ | s) <;> rfl

end AxiomaticGW.GluingExpression
