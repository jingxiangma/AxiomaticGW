/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCachedTerms
public import AxiomaticGW.Tautological.L24Terms

/-!
# Executable complete L24 surface equations

The full coefficient and graph data use the existing surface contraction and
low-genus algorithms. Support and evaluation commute with the executable sum.
`Surfaces.L24` supplies geometric soundness under the original source inputs.
-/

@[expose] public section

namespace AxiomaticGW.L24Relation
open GluingExpression RelationCertificate PsiBoundaryExpansion

-- The finite source uses the same reduction depth as its checked graph frame.
set_option maxRecDepth 20000

/-- Full raw surface equation, retaining all original and pullback multiplicities. -/
def surfaceTerms {σ : Type*} (X : SurfaceTarget)
    (vertex : SurfaceVertexValues X (RationalTerms σ)) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms σ :=
  (cotangentRelation.pullback n).bind fun t ↦ RationalTerms.scale t.1
    (t.2.expression.surfaceDecoratedTerms X vertex t.2.decoration beta k a)

/-- Exact rational evaluation commutes with every full-class decorated contraction. -/
theorem eval_surfaceTerms {σ B : Type*} [CommRing B] [Algebra ℚ B]
    (v : σ → B) (X : SurfaceTarget) (vertex : SurfaceVertexValues X (RationalTerms σ))
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms.eval v (surfaceTerms X vertex n beta k a) =
      ((cotangentRelation.pullback n).map fun t ↦ algebraMap ℚ B t.1 *
        t.2.expression.surfaceDecoratedEval X
          (fun g S _ h beta k a ↦ RationalTerms.eval v (vertex g S h beta k a))
          t.2.decoration beta k a).sum := by
  have hbind {ι : Type 1} (s : Multiset ι) (f : ι → RationalTerms σ) :
      RationalTerms.eval v (s.bind f) = (s.map (fun i ↦ RationalTerms.eval v (f i))).sum := by
    simp only [RationalTerms.eval, Multiset.map_bind, Multiset.sum_bind]
  simp only [surfaceTerms, hbind, RationalTerms.eval_scale,
    GluingExpression.eval_surfaceDecoratedTerms]

/-- Execute dimension reduction and the proved low-genus algorithms at every component. -/
def genusTwoTerms (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms (SurfaceAncestorKey X) :=
  surfaceTerms X (SurfaceGenusTwo.vertexTerms X) n beta k a

/-- Reuse selected component reconstructions in the same complete graph equation. -/
def genusTwoTermsCached (X : SurfaceTarget) (queries : Finset (SurfaceAncestorKey X))
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms (SurfaceAncestorKey X) :=
  let cache := SurfaceGenusTwo.ResidualCache.ofQueries X queries
  surfaceTerms X (SurfaceGenusTwo.cachedVertexTerms X cache) n beta k a

/-- Cached expansion retains the complete uncollected expression, without new hypotheses. -/
theorem genusTwoTermsCached_eq (X : SurfaceTarget) (queries : Finset (SurfaceAncestorKey X))
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    genusTwoTermsCached X queries n beta k a = genusTwoTerms X n beta k a := by
  rw [genusTwoTermsCached, SurfaceGenusTwo.cachedVertexTerms_eq]
  rfl

/-- Every monomial is affine in dimension-compatible genus-two variables, with an
 effective remainder in the original full curve class, at arbitrary markings and powers. -/
theorem genusTwoTerms_bound (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    SurfaceGenusTwo.TermsBound 2 beta (genusTwoTerms X n beta k a) := by
  apply SurfaceGenusTwo.termsBound_bind
  intro t _
  exact SurfaceGenusTwo.termsBound_scale
    (SurfaceGenusTwo.termsBound_decorated t.2.expression t.2.decoration beta k a) t.1

end AxiomaticGW.L24Relation
