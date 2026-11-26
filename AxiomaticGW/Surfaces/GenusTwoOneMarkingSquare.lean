/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoAncestorCertificate
public import AxiomaticGW.Surfaces.GenusTwoConstant
public import AxiomaticGW.Surfaces.GenusTwoOneMarkingKey

/-! # Scalar reduction of a one-marked square in the terminating ancestor evaluator

The ten graphs of the original relation have only genus-zero and genus-one components.
Thus the evaluator's dimension guards can be retained while dispensing with every
residual polynomial and genus-two terminal in this sector.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open GenusTwoPsiSquare GluingExpression
variable {X : SurfaceTarget}

private theorem boundaryRemainder_zero : boundaryRemainder 0 = signedBoundary := by
  simp only [boundaryRemainder, psiBoundary, fundamentalCorrections, Multiset.map_zero, zero_add,
    CotangentCombination.pullback, CotangentTerm.addMarkings, Multiset.map_singleton, Int.cast_one,
    mul_one, Multiset.bind_singleton, Multiset.map_id']

/-- Scalar contraction of all ten boundary graphs for a singleton after removing two psi powers. -/
def oneMarkingSquareValue (beta : X.Curve) (a : SurfaceBasisLabel X) (k : ℕ) : ℚ :=
  ∑ i, boundary (boundaryIndex i) * (boundaryTerm i).1.surfaceDecoratedEval X (constantVertex X)
    (boundaryTerm i).2 beta (fun _ ↦ k) (fun _ ↦ a)

private theorem eval_single_boundary (v : SurfaceAncestorKey X → ℚ)
    (beta : X.Curve) (a : SurfaceBasisLabel X) (k : ℕ) :
    RationalTerms.eval v (boundaryReductionTerms X (boundaryRemainder 0) beta
      (fun _ ↦ k) (fun _ ↦ a)) = oneMarkingSquareValue beta a k := by
  have hbind {σ : Type 1} (s : Multiset σ) (f : σ → RationalTerms (SurfaceAncestorKey X)) :
      RationalTerms.eval v (s.bind f) = (s.map fun i ↦ RationalTerms.eval v (f i)).sum := by
    simp only [RationalTerms.eval, Multiset.map_bind, Multiset.sum_bind]
  simp only [boundaryRemainder_zero, signedBoundary, boundaryReductionTerms, hbind,
    RationalTerms.eval_scale, Algebra.algebraMap_self_apply, Multiset.map_map,
    Function.comp_def, neg_neg, boundaryCotangentTerm, eval_surfaceDecoratedTerms,
    oneMarkingSquareValue, Finset.sum_eq_multiset_sum]
  apply congrArg Multiset.sum
  apply congrArg (fun f ↦ Multiset.map f (Finset.univ : Finset (Fin 10)).val)
  funext i
  apply congrArg (boundary (boundaryIndex i) * ·)
  apply surfaceDecoratedEval_congr_of_genus
  intro g S _ h gamma e b hg
  have hg' := hg.trans (boundaryTerm_genus i)
  unfold vertexTerms residualTerms constantVertex
  simp only [SurfaceAncestorKey.ofLabels, hg', if_true]
  split_ifs <;> simp only [RationalTerms.eval_term, RationalTerms.eval_zero,
    Multiset.map_zero, Multiset.prod_zero, Algebra.algebraMap_self_apply, mul_one]

/-- The terminating ancestor evaluator agrees with the scalar square reduction for every
surface, full class and state. Its answer in this sector is independent of the terminal family. -/
theorem ancestorValue_oneMarking_square (base : SurfaceAncestorKey X → ℚ)
    (beta : X.Curve) (a : SurfaceBasisLabel X) (k : ℕ) :
    ancestorValue base (oneMarkingKey beta a (k + 2)) = oneMarkingSquareValue beta a k := by
  let q := oneMarkingKey beta a (k + 2)
  have hk : 1 < q.totalPsi := by
    change 1 < k + 2
    omega
  let z : Fin q.orderedInsertions.length := ⟨0, by change 0 < 1; decide⟩
  have hz (j : Fin q.orderedInsertions.length) : j = z := by
    apply Fin.ext
    have hj := j.isLt
    change j.val < 1 at hj
    change j.val = 0
    omega
  have hs : (squareMarks q).Nonempty := by
    refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change 2 ≤ k + 2
    omega
  rw [ancestorValue_step base q rfl hk, ancestorStep, ancestorReductionTerms, dif_pos hs]
  have hl : q.orderedLabels ∘ squareFrame q hs = fun _ ↦ a := by
    funext i
    have hi : squareFrame q hs i = z := hz _
    rw [Function.comp_apply, hi]
    rfl
  have hp : squareLowerPowers q hs = fun _ ↦ k := by
    funext i
    have hi : squareFrame q hs i = z := hz _
    simp only [squareLowerPowers, Pi.sub_apply, Function.comp_apply, hi]
    change k + 2 - 2 = k
    omega
  rw [hl, hp]
  exact eval_single_boundary _ beta a k

end AxiomaticGW.SurfaceGenusTwo
