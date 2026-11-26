/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoAncestorCertificate

/-! # The original two-marked genus-two ancestor product

At total cotangent degree two, the twenty-five boundary graphs evaluate directly
against the low-power genus-two terminal family. The genus-two component of
the rational-tail graph is retained with its node cotangent power.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open GluingExpression GenusTwoPsiProduct
variable {X : SurfaceTarget}

/-- One weighted contraction from the original two-marked psi-product relation. -/
def productGraph (v : SurfaceVertexValues X ℚ) (beta : X.Curve)
    (labels : Fin 2 → SurfaceBasisLabel X) (i : Fin 25) : ℚ :=
  boundary (boundaryIndex i) * (boundaryTerm i).1.surfaceDecoratedEval X v
    (boundaryTerm i).2 beta 0 labels

/-- Scalar substitution at every actual component, including genus two. -/
def productVertex (base : SurfaceAncestorKey X → ℚ) : SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦ RationalTerms.eval base (vertexTerms X g S h beta k a)

private theorem product_boundary_zero : boundaryRemainder 0 = signedBoundary := by
  simp only [boundaryRemainder, psiBoundary, fundamentalCorrections, Multiset.map_zero, zero_add,
    CotangentCombination.pullback, CotangentTerm.addMarkings, Multiset.map_singleton, Int.cast_one,
    mul_one, Multiset.bind_singleton, Multiset.map_id']

private theorem eval_product_boundary (base : SurfaceAncestorKey X → ℚ) (n : ℕ) (hn : n = 0)
    (beta : X.Curve) (a : ExtraMarkings n (Fin 2) → SurfaceBasisLabel X) :
    RationalTerms.eval base (boundaryReductionTerms X (boundaryRemainder n) beta 0 a) =
      ∑ i, productGraph (productVertex base) beta (a ∘ ExtraMarkings.oldLabel n) i := by
  subst n
  have hbind {σ : Type 1} (s : Multiset σ) (f : σ → RationalTerms (SurfaceAncestorKey X)) :
      RationalTerms.eval base (s.bind f) = (s.map fun i ↦ RationalTerms.eval base (f i)).sum := by
    simp only [RationalTerms.eval, Multiset.map_bind, Multiset.sum_bind]
  simp only [product_boundary_zero, signedBoundary, boundaryReductionTerms, hbind,
    RationalTerms.eval_scale, Algebra.algebraMap_self_apply, Multiset.map_map,
    Function.comp_def, neg_neg, boundaryCotangentTerm, eval_surfaceDecoratedTerms,
    productGraph, Finset.sum_eq_multiset_sum]
  rfl

/-- A two-marked product in the selected frame is exactly the sum of its signed
graphs. Every residual genus-two query is low-power after this one step. -/
theorem ancestorValue_twoMarking_product (base : SurfaceAncestorKey X → ℚ)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) (hn : q.orderedInsertions.length = 2)
    (hp : q.totalPsi = 2) (hs : ¬ (squareMarks q).Nonempty)
    (labels : Fin 2 → SurfaceBasisLabel X)
    (ha : q.orderedLabels (firstProductMark q (by omega)) = labels 0)
    (hb : q.orderedLabels (secondProductMark q (by omega) hs) = labels 1) :
    ancestorValue base q = ∑ i, productGraph (productVertex base) q.beta labels i := by
  have hk : 1 < q.totalPsi := by omega
  rw [ancestorValue_step base q hg hk, ancestorStep_congr (ancestorValue base) base q hk
    (fun r hgen hpow ↦ ancestorValue_low base r hgen (by omega)),
    ancestorStep, ancestorReductionTerms, dif_neg hs]
  have hsum := sum_productLowerPowers q hk hs
  have hz : productLowerPowers q hk hs = 0 := by
    funext j
    have hle := Finset.single_le_sum (f := productLowerPowers q hk hs)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    change productLowerPowers q hk hs j = 0
    omega
  rw [hz, eval_product_boundary base _ (by omega)]
  have he : (q.orderedLabels ∘ productFrame q hk hs) ∘
      ExtraMarkings.oldLabel (q.orderedInsertions.length - 2) = labels := by
    funext j
    fin_cases j
    · exact (congrArg q.orderedLabels (productFrame_old_zero q hk hs)).trans ha
    · exact (congrArg q.orderedLabels (productFrame_old_one q hk hs)).trans hb
  rw [he]

end AxiomaticGW.SurfaceGenusTwo
