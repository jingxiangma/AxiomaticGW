/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoTwoMarkingProduct
public import AxiomaticGW.Surfaces.ScalarExternalGraph

/-! # Scalar contraction of the complete pulled-back square relation

The new marking can lie on any component or on a rational-tail correction.
The genus-two vertex in the correction of the smooth leading square is
evaluated at its actual attaching flag.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open GluingExpression
variable {X : SurfaceTarget}

/-- Each signed summand in the pulled square keeps its decoration and all external powers. -/
def pulledSquare (v : SurfaceVertexValues X ℚ) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 1) → ℕ) (a : ExtraMarkings n (Fin 1) → SurfaceBasisLabel X) : ℚ :=
  ((GenusTwoPsiSquare.boundaryRemainder n).map fun t ↦
    -t.1 * t.2.expression.surfaceDecoratedEval X v t.2.decoration beta k a).sum

/-- The leading-term correction comes first, followed by the ten original boundary sources.
Each source includes all placements and new rational tails from the added markings. -/
def pulledSquarePart (v : SurfaceVertexValues X ℚ) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 1) → ℕ) (a : ExtraMarkings n (Fin 1) → SurfaceBasisLabel X) :
    Fin 11 → ℚ := Fin.cases
  (((fundamentalCorrections GenusTwoPsiSquare.stableArity (fun _ : Fin 1 ↦ 2) n).map
    fun t ↦ -(t.1 : ℚ) * externalScalar X v t.2 beta k a).sum)
  (fun i ↦ (((GenusTwoPsiSquare.boundaryCotangentTerm i).addMarkings n).map
    fun t ↦ -(-GenusTwoPsiSquare.boundary (GenusTwoPsiSquare.boundaryIndex i) * (t.1 : ℚ)) *
      externalScalar X v t.2 beta k a).sum)

/-- The source-by-source partition is exactly the full signed pullback. -/
theorem pulledSquare_eq_parts (v : SurfaceVertexValues X ℚ) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 1) → ℕ) (a : ExtraMarkings n (Fin 1) → SurfaceBasisLabel X) :
    pulledSquare v n beta k a = ∑ i, pulledSquarePart v n beta k a i := by
  rw [Fin.sum_univ_succ]
  simp only [pulledSquare, pulledSquarePart, GenusTwoPsiSquare.boundaryRemainder, psiBoundary,
    GenusTwoPsiSquare.signedBoundary, CotangentCombination.pullback, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map, Multiset.map_bind, Multiset.sum_bind,
    Multiset.bind_map, Function.comp_def, Fin.cases_zero, Fin.cases_succ,
    Finset.sum_eq_multiset_sum, externalScalar_eq]

private theorem eval_pulledSquare (v : SurfaceAncestorKey X → ℚ) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 1) → ℕ) (a : ExtraMarkings n (Fin 1) → SurfaceBasisLabel X) :
    RationalTerms.eval v (boundaryReductionTerms X (GenusTwoPsiSquare.boundaryRemainder n)
      beta k a) = pulledSquare (productVertex v) n beta k a := by
  have hbind {σ : Type 1} (s : Multiset σ) (f : σ → RationalTerms (SurfaceAncestorKey X)) :
      RationalTerms.eval v (s.bind f) = (s.map fun i ↦ RationalTerms.eval v (f i)).sum := by
    simp only [RationalTerms.eval, Multiset.map_bind, Multiset.sum_bind]
  simp only [boundaryReductionTerms, hbind, RationalTerms.eval_scale, eval_surfaceDecoratedTerms,
    Algebra.algebraMap_self_apply, pulledSquare]
  rfl

/-- Any selected square in the original recursive evaluator admits direct scalar substitution
at every component of its complete universal-curve pullback. -/
theorem ancestorValue_pulledSquare (v : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) (hk : 1 < q.totalPsi) (hs : (squareMarks q).Nonempty) :
    ancestorValue v q =
      pulledSquare (productVertex (ancestorValue v)) (q.orderedInsertions.length - 1) q.beta
        (squareLowerPowers q hs) (q.orderedLabels ∘ squareFrame q hs) := by
  rw [ancestorValue_step v q hg hk, ancestorStep, ancestorReductionTerms, dif_pos hs,
    eval_pulledSquare]

end AxiomaticGW.SurfaceGenusTwo
