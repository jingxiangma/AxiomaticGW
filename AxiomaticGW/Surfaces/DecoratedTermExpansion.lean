/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.TermExpansion
public import AxiomaticGW.Surfaces.DecoratedGluingEvaluation

/-!
# Exact terms for cotangent-decorated surface contractions

The existing rational term format is expanded along the actual gluing
expression. Both node branches, all full curve splittings, signed metric
entries and repeated monomials are retained. Evaluation commutes with this
expansion for every terminal substitution, including partial reconstruction.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

/-- The decorated counterpart of `surfaceTerms`, in the same exact term format. -/
def surfaceDecoratedTerms {σ : Type*} (X : SurfaceTarget)
    (vertex : SurfaceVertexValues X (RationalTerms σ))
    {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → X.Curve → (S → ℕ) →
      (S → SurfaceBasisLabel X) → RationalTerms σ
  | @fundamental g S _ h, d, beta, k, a => vertex g S h beta (k + d) a
  | @relabel _ _ _ _ _ e x, d, beta, k, a =>
      x.surfaceDecoratedTerms X vertex d beta (k ∘ e) (a ∘ e)
  | @separating _ _ _ _ _ _ x y, d, beta, k, a =>
      ∑ split ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
        RationalTerms.scale b.inverseWeight
          (RationalTerms.mul
            (x.surfaceDecoratedTerms X vertex d.1 split.1 (PsiClasses.separatingLeftPowers k)
              (Option.elim · b (a ∘ Sum.inl)))
            (y.surfaceDecoratedTerms X vertex d.2 split.2 (PsiClasses.separatingRightPowers k)
              (Option.elim · b.dual (a ∘ Sum.inr))))
  | @nonseparating _ _ _ x, d, beta, k, a =>
      ∑ b : SurfaceBasisLabel X, RationalTerms.scale b.inverseWeight
        (x.surfaceDecoratedTerms X vertex d beta (PsiClasses.nonseparatingPowers k)
          (Option.elim · b (fun t ↦ Option.elim t b.dual a)))

/-- Every exact expansion denotes the original decorated contraction. -/
theorem eval_surfaceDecoratedTerms {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (X : SurfaceTarget) (vertex : SurfaceVertexValues X (RationalTerms σ))
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (d : x.CotangentDecoration)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    RationalTerms.eval v (x.surfaceDecoratedTerms X vertex d beta k a) =
      x.surfaceDecoratedEval X
        (fun g S _ h beta k a ↦ RationalTerms.eval v (vertex g S h beta k a)) d beta k a := by
  induction x generalizing beta with
  | fundamental g S h => rfl
  | relabel e x ih => exact ih d beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    simp only [surfaceDecoratedTerms, surfaceDecoratedEval, RationalTerms.eval_sum,
      RationalTerms.eval_scale, RationalTerms.eval_mul, ihx, ihy]
  | nonseparating x ih =>
    simp only [surfaceDecoratedTerms, surfaceDecoratedEval, RationalTerms.eval_sum,
      RationalTerms.eval_scale, ih]

/-- With zero component decorations the existing term expansion is recovered exactly. -/
theorem surfaceDecoratedTerms_zeroDecoration {σ : Type*} (X : SurfaceTarget)
    (vertex : SurfaceVertexValues X (RationalTerms σ))
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    x.surfaceDecoratedTerms X vertex x.zeroDecoration beta k a =
      x.surfaceTerms X vertex beta k a := by
  induction x generalizing beta with
  | fundamental g S h =>
    change vertex g S h beta (k + 0) a = vertex g S h beta k a
    rw [add_zero]
  | relabel e x ih => exact ih beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    simp only [surfaceDecoratedTerms, zeroDecoration, surfaceTerms, ihx, ihy]
  | nonseparating x ih =>
    simp only [surfaceDecoratedTerms, zeroDecoration, surfaceTerms, ih]

end AxiomaticGW.GluingExpression
