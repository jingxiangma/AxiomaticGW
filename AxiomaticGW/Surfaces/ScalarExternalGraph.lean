/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ZeroPointContraction
public import AxiomaticGW.Surfaces.DecoratedGluingEvaluation

/-! # Effective-coordinate evaluation of graphs with external cotangent powers

External powers transport down each edge before they are added to the
original graph decoration. The coordinate contraction retains each full
curve splitting and skips a factor only after its partner vanishes.
-/

@[expose] public section
namespace AxiomaticGW.GluingExpression

/-- Add the pulled-back exterior powers to the component decorations at their actual vertices. -/
def withExternalPowers : {g : ℕ} → {S : Type} → [Fintype S] → (z : GluingExpression g S) →
    z.CotangentDecoration → (S → ℕ) → z.CotangentDecoration
  | _, _, _, @fundamental _ _ _ _, d, k => k + d
  | _, _, _, @relabel _ _ _ _ _ e x, d, k => withExternalPowers x d (k ∘ e)
  | _, _, _, @separating _ _ _ _ _ _ x y, d, k =>
    (withExternalPowers x d.1 (PsiClasses.separatingLeftPowers k),
     withExternalPowers y d.2 (PsiClasses.separatingRightPowers k))
  | _, _, _, @nonseparating _ _ _ x, d, k =>
    withExternalPowers x d (PsiClasses.nonseparatingPowers k)

/-- Use the zero-extra-point contraction once every exterior power is on its component. -/
def externalScalar (X : SurfaceTarget) (v : SurfaceVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] (z : CotangentTerm g S) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) : ℚ :=
  z.expression.zeroPointContraction X (fun g S _ h d _ b x ↦ v g S h b d x)
    (z.expression.withExternalPowers z.decoration k) z.labels beta a

theorem externalScalar_eq (X : SurfaceTarget) (v : SurfaceVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] (z : CotangentTerm g S) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    externalScalar X v z beta k a =
      z.expression.surfaceDecoratedEval X v z.decoration beta k a := by
  obtain ⟨x, d, l⟩ := z
  unfold externalScalar
  change zeroPointContraction X _ x (withExternalPowers x d k) l beta a =
    x.surfaceDecoratedEval X v d beta k a
  induction x generalizing beta with
  | fundamental => rfl
  | relabel e x ih => exact ih beta (k ∘ e) (a ∘ e) d l
  | separating x y ihx ihy =>
    have skip (c d : ℚ) : (if d = 0 then 0 else c * d) = c * d := by
      split_ifs with h
      · rw [h, mul_zero]
      · rfl
    simp only [withExternalPowers, zeroPointContraction, surfaceDecoratedEval, skip, ihx, ihy,
      Algebra.algebraMap_self_apply]
    rw [SurfaceTarget.sumSubcurves_eq, SurfaceTarget.splittings, WeightedCurveClass.splittings,
      Finset.sum_image (fun _ _ _ _ h ↦ congrArg Prod.fst h)]
  | nonseparating x ih =>
    simp only [withExternalPowers, zeroPointContraction, surfaceDecoratedEval, ih,
      Algebra.algebraMap_self_apply]

end AxiomaticGW.GluingExpression
