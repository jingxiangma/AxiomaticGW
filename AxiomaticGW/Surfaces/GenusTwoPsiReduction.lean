/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPsiSupport

/-!
# Surface reductions from the original genus-two psi generators

The full square and product relations isolate an ancestor with two selected
cotangent powers. The right-hand side uses the original signed boundary,
including every marking pullback and rational-tail correction. The support
theorem in the preceding module proves strict psi descent. Soundness here
uses the original geometric generators and the existing lower-genus
identifications, without an assumed genus-two recurrence or new seed.
-/

@[expose] public section

namespace AxiomaticGW
open GluingExpression RelationCertificate PsiBoundaryExpansion SurfaceGenusTwo
attribute [local instance] strataRealizationModule

private theorem reduction_of_contraction {X : SurfaceTarget}
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {I : StableCurveIntegration C} (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (hone : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
      SurfaceGenusOne.ancestorValue X q = q.eval Omega P I)
    {S : Type} [Fintype S] [DecidableEq S] (h : StableArity 2 S) (d : S → ℕ)
    (b : CotangentCombination 2 S) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X)
    (hrel : ({(1, CotangentTerm.fundamental 2 S h d)} + b).gwContraction
      Omega P I beta k (fun s ↦ (a s).value) = 0) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I)
      (boundaryReductionTerms X b beta k a) =
      Omega.ancestorInvariant P I 2 S h beta (k + d) (fun s ↦ (a s).value) := by
  have hv := eval_boundaryReductionTerms P T hzero hone b beta k a
  have hs : Omega.ancestorInvariant P I 2 S h beta (k + d) (fun s ↦ (a s).value) +
      b.gwContraction Omega P I beta k (fun s ↦ (a s).value) = 0 := by
    simpa only [CotangentCombination.gwContraction, Multiset.map_add, Multiset.sum_add,
      Multiset.map_singleton, Multiset.sum_singleton, one_smul,
      CotangentTerm.fundamental, gwDecoratedAncestorContraction] using hrel
  exact hv.trans (eq_neg_of_add_eq_zero_left hs).symm

namespace GenusTwoPsiSquare

/-- Surface interpretation of the complete marked square reduction from
the six original interior rows and the original elliptic boundary source. -/
theorem reduction_eq_ancestor_from_generators {X : SurfaceTarget}
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {I : StableCurveIntegration C}
    (p : Exchange) (hp : AcceptsExchange p)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (H : TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hEL : (A 1 (Fin 1)).RelabelCompatible (A 1 (Option (Fin 0)))
      GenusOnePsi.stableArity ellipticSourceStable (finSuccEquiv 0))
    (hLB : (A 1 (Option (Fin 0))).SeparatingCompatible (A 1 (Option (Fin 1)))
      (A 2 (Fin 0 ⊕ Fin 1)) F ellipticSourceStable ellipticMarkedStable)
    (hUA : (A 2 (Fin 0 ⊕ Fin 1)).RelabelCompatible (A 2 (Fin 1))
      separatingStable stableArity (Equiv.emptySum (Fin 0) (Fin 1)))
    (hinterior : ∀ i : Fin 6, (A 2 (Fin 1)).map (interpret columns (rows i.castSucc)) = 0)
    (hsource : (A 1 (Fin 1)).map
      (interpret GenusOnePsi.columns (GenusOnePsi.rows 0)) = 0)
    (n : ℕ) (hin : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (hone : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
      SurfaceGenusOne.ancestorValue X q = q.eval Omega P I)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 1) → ℕ)
    (a : ExtraMarkings n (Fin 1) → SurfaceBasisLabel X) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I)
      (boundaryReductionTerms X (boundaryRemainder n) beta k a) =
      Omega.ancestorInvariant P I 2 (ExtraMarkings n (Fin 1)) (stableArity.extraMarkings n)
        beta (k + markedPowers (fun _ : Fin 1 ↦ 2) n) (fun s ↦ (a s).value) := by
  letI := ExtraMarkings.decidableEq (Fin 1) n
  have hclass := realized_relation_with_markings_from_generators p hp A F N P K hK H G
    hEL hLB hUA hinterior hsource n hin hout
  have hc : ∀ t ∈ cotangentRelation.pullback n,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P := by
    intro t ht
    obtain ⟨z, hz, w, hw, rfl⟩ := (CotangentCombination.mem_pullback _ n t).mp ht
    exact hout z hz w hw
  have he := CotangentCombination.gwContraction_eq_zero A F N Omega P
    (cotangentRelation.pullback n) (stableArity.extraMarkings n) hc hclass
    beta k (fun s ↦ (a s).value)
  rw [pullback_eq_leading_add_boundary] at he
  exact reduction_of_contraction P T hzero hone (stableArity.extraMarkings n)
    (markedPowers (fun _ : Fin 1 ↦ 2) n) (boundaryRemainder n) beta k a he

end GenusTwoPsiSquare

namespace GenusTwoPsiProduct

/-- Surface interpretation of the complete marked product reduction from
the ten original interior rows and the three original boundary sources. -/
theorem reduction_eq_ancestor_from_generators {X : SurfaceTarget}
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {I : StableCurveIntegration C}
    (p : Exchange) (hp : AcceptsExchange p)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (H : TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hc : ∀ b, SourceCompatible A F b)
    (hsource : ∀ b, (A (BelorousskiPandharipande.sourceGenus (sourceFamily b))
      (Fin (BelorousskiPandharipande.sourceArity (sourceFamily b)))).map
        (BelorousskiPandharipande.sourceExpression (sourceIndex b)) = 0)
    (hinterior : ∀ i : Fin 10,
      (A 2 (Fin 2)).map (interpret columns (rows (i.castLE (by decide)))) = 0)
    (n : ℕ) (hin : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (hone : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
      SurfaceGenusOne.ancestorValue X q = q.eval Omega P I)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 2) → ℕ)
    (a : ExtraMarkings n (Fin 2) → SurfaceBasisLabel X) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I)
      (boundaryReductionTerms X (boundaryRemainder n) beta k a) =
      Omega.ancestorInvariant P I 2 (ExtraMarkings n (Fin 2)) (stableArity.extraMarkings n)
        beta (k + markedPowers (fun _ : Fin 2 ↦ 1) n) (fun s ↦ (a s).value) := by
  letI := ExtraMarkings.decidableEq (Fin 2) n
  have hclass := realized_relation_with_markings_from_generators p hp A F N P K hK H G
    hc hsource hinterior n hin hout
  have hterms : ∀ t ∈ cotangentRelation.pullback n,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P := by
    intro t ht
    obtain ⟨z, hz, w, hw, rfl⟩ := (CotangentCombination.mem_pullback _ n t).mp ht
    exact hout z hz w hw
  have he := CotangentCombination.gwContraction_eq_zero A F N Omega P
    (cotangentRelation.pullback n) (stableArity.extraMarkings n) hterms hclass
    beta k (fun s ↦ (a s).value)
  rw [pullback_eq_leading_add_boundary] at he
  exact reduction_of_contraction P T hzero hone (stableArity.extraMarkings n)
    (markedPowers (fun _ : Fin 2 ↦ 1) n) (boundaryRemainder n) beta k a he

end GenusTwoPsiProduct
end AxiomaticGW
