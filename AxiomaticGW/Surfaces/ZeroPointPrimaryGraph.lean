/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ZeroPointContraction
public import AxiomaticGW.Surfaces.GenusTwoPrimaryConstant

/-!
# Recognizing primary components of decorated scalar contractions

Undecorated low-genus graphs at zero extra points can use the existing
dimension-selected primary graph evaluator. The test traverses all vertices
and their cotangent decorations, including node flags.
-/

@[expose] public section
namespace AxiomaticGW.GluingExpression

/-- Test whether every cotangent decoration on every component is zero. -/
def noCotangent : {g : ℕ} → {S : Type} → [Fintype S] → (x : GluingExpression g S) →
    x.CotangentDecoration → Bool
  | _, _, _, @fundamental _ _ _ _, d => decide (d = 0)
  | _, _, _, @relabel _ _ _ _ _ _ x, d => noCotangent x d
  | _, _, _, @separating _ _ _ _ _ _ x y, d => noCotangent x d.1 && noCotangent y d.2
  | _, _, _, @nonseparating _ _ _ x, d => noCotangent x d

theorem noCotangent_eq_true {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) : x.noCotangent d = true ↔ d = x.zeroDecoration := by
  induction x with
  | fundamental => exact decide_eq_true_iff
  | relabel e x ih => exact ih d
  | separating x y ihx ihy =>
    simp only [noCotangent, Bool.and_eq_true, ihx, ihy, zeroDecoration, Prod.ext_iff]
  | nonseparating x ih => exact ih d

/-- The dimension-pruned evaluator computes the same scalar as the complete zero-point graph. -/
theorem primaryGraph_eq_zeroPoint (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (d : x.CotangentDecoration)
    (l : x.DecidableLabels) (beta : X.Curve) (a : S → SurfaceBasisLabel X)
    (hg : x.maxComponentGenus ≤ 1) (hd : x.noCotangent d = true) :
    SurfaceGenusOne.primaryGraphDimensionEval X v₀ v₁ x beta 0 a =
      x.zeroPointContraction X (SurfacePointPullback.vertex X (SurfaceGenusTwo.constantVertex X) 0)
        d l beta a := by
  rw [(noCotangent_eq_true x d).mp hd, zeroPointContraction_eq,
    SurfaceGenusOne.primaryGraphDimensionEval_eq,
    SurfaceGenusTwo.primaryGraphEval_pointContraction_eq X v₀ v₁ x hg,
    SurfaceGenusTwo.primaryConstantPointVertex_eq X v₀ v₁ h₀ h₁]

end AxiomaticGW.GluingExpression
