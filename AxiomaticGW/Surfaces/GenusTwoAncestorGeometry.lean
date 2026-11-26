/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoAncestors

/-!
# Geometric interpretation of the genus-two ancestor recursion

The selected square/product equation is transported through the actual query
frame, preserving every state/power occurrence. Original geometric generators
therefore identify the recursive step with the ancestor invariant. The final
target-specific consumer must supply the low-psi family and the already
reconstructed lower genera from their named geometric inputs and finite seeds.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open GluingExpression RelationCertificate PsiBoundaryExpansion
attribute [local instance] strataRealizationModule

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {I : StableCurveIntegration C}

/-- A numbered occurrence frame transports the powers and basis states together. -/
theorem ancestorInvariant_in_frame (P : PsiClasses C) (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) {S : Type} [Fintype S] (h : StableArity 2 S)
    (e : S ≃ Fin q.orderedInsertions.length) :
    Omega.ancestorInvariant P I 2 S h q.beta (q.orderedPowers ∘ e)
      (fun s ↦ (q.orderedLabels (e s)).value) = q.eval Omega P I := by
  have hn : StableArity 2 (Fin q.orderedInsertions.length) := by
    simp only [StableArity, Fintype.card_fin]
    omega
  have hr := congrArg (fun f ↦ f (fun s ↦ (q.orderedLabels s).value))
    (Omega.ancestorInvariant_relabel P I 2 S (Fin q.orderedInsertions.length)
      h hn e q.beta (q.orderedPowers ∘ e))
  simp only [MultilinearMap.domDomCongr_apply, Function.comp_apply,
    Equiv.apply_symm_apply] at hr
  have hq : SurfaceAncestorKey.ofLabels 2 (Fin q.orderedInsertions.length) hn q.beta
      q.orderedPowers q.orderedLabels = q := by
    apply (SurfaceAncestorKey.eq_iff _ _).mpr
    refine ⟨hg.symm, rfl, ?_⟩
    have he := congrArg SurfaceAncestorKey.insertions q.of_ordered_eq
    exact he
  have hi := SurfaceAncestorKey.eval_ofLabels Omega P I 2 _ hn q.beta
    q.orderedPowers q.orderedLabels
  rw [hq] at hi
  exact hr.trans hi.symm

section Geometry

variable (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
  (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (K : PsiForgetFormula P) (hK : TailCompatible K F N)
  (HF : TailForgetCompatible C) (J : GluingForgetfulCompatibility F N)
  (pS : GenusTwoPsiSquare.Exchange) (hpS : GenusTwoPsiSquare.AcceptsExchange pS)
  (hELS : (Z 1 (Fin 1)).RelabelCompatible (Z 1 (Option (Fin 0)))
    GenusOnePsi.stableArity GenusTwoPsiSquare.ellipticSourceStable (finSuccEquiv 0))
  (hLBS : (Z 1 (Option (Fin 0))).SeparatingCompatible (Z 1 (Option (Fin 1)))
    (Z 2 (Fin 0 ⊕ Fin 1)) F GenusTwoPsiSquare.ellipticSourceStable
      GenusTwoPsiSquare.ellipticMarkedStable)
  (hUAS : (Z 2 (Fin 0 ⊕ Fin 1)).RelabelCompatible (Z 2 (Fin 1))
    GenusTwoPsiSquare.separatingStable GenusTwoPsiSquare.stableArity
      (Equiv.emptySum (Fin 0) (Fin 1)))
  (hinteriorS : ∀ i : Fin 6, (Z 2 (Fin 1)).map
    (interpret GenusTwoPsiSquare.columns (GenusTwoPsiSquare.rows i.castSucc)) = 0)
  (hsourceS : (Z 1 (Fin 1)).map
    (interpret GenusOnePsi.columns (GenusOnePsi.rows 0)) = 0)
  (hinS : ∀ t ∈ GenusTwoPsiSquare.cotangentRelation,
    t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
  (houtS : ∀ n t, t ∈ GenusTwoPsiSquare.cotangentRelation → ∀ z ∈ t.2.addMarkings n,
    z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
  (pP : GenusTwoPsiProduct.Exchange) (hpP : GenusTwoPsiProduct.AcceptsExchange pP)
  (hcP : ∀ b, GenusTwoPsiProduct.SourceCompatible Z F b)
  (hsourceP : ∀ b, (Z (BelorousskiPandharipande.sourceGenus (GenusTwoPsiProduct.sourceFamily b))
    (Fin (BelorousskiPandharipande.sourceArity (GenusTwoPsiProduct.sourceFamily b)))).map
      (BelorousskiPandharipande.sourceExpression (GenusTwoPsiProduct.sourceIndex b)) = 0)
  (hinteriorP : ∀ i : Fin 10, (Z 2 (Fin 2)).map
    (interpret GenusTwoPsiProduct.columns
      (GenusTwoPsiProduct.rows (Fin.castAdd 3 i))) = 0)
  (hinP : ∀ t ∈ GenusTwoPsiProduct.cotangentRelation,
    t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
  (houtP : ∀ n t, t ∈ GenusTwoPsiProduct.cotangentRelation → ∀ z ∈ t.2.addMarkings n,
    z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
  (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
    SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
  (hone : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
    SurfaceGenusOne.ancestorValue X q = q.eval Omega P I)

include P T Z F N K hK HF J pS hpS hELS hLBS hUAS hinteriorS hsourceS hinS houtS
  pP hpP hcP hsourceP hinteriorP hinP houtP hzero hone

/-- Both branches of the executable selector are the original geometric
equations in the requested occurrence frame; no recurrence is assumed. -/
theorem ancestorStep_eval (q : SurfaceAncestorKey X) (hg : q.genus = 2)
    (hk : 1 < q.totalPsi) :
    ancestorStep (SurfaceAncestorKey.eval Omega P I) q hk = q.eval Omega P I := by
  unfold ancestorStep ancestorReductionTerms
  split_ifs with hs
  · have he := GenusTwoPsiSquare.reduction_eq_ancestor_from_generators pS hpS Z F N P T K hK
      HF J hELS hLBS hUAS hinteriorS hsourceS (q.orderedInsertions.length - 1) hinS
      (houtS (q.orderedInsertions.length - 1)) hzero hone q.beta (squareLowerPowers q hs)
      (q.orderedLabels ∘ squareFrame q hs)
    rw [squareLowerPowers_restore] at he
    exact he.trans (ancestorInvariant_in_frame P q hg _ (squareFrame q hs))
  · have he := GenusTwoPsiProduct.reduction_eq_ancestor_from_generators pP hpP Z F N P T K hK
      HF J hcP hsourceP hinteriorP (q.orderedInsertions.length - 2) hinP
      (houtP (q.orderedInsertions.length - 2)) hzero hone q.beta (productLowerPowers q hk hs)
      (q.orderedLabels ∘ productFrame q hk hs)
    rw [productLowerPowers_restore] at he
    exact he.trans (ancestorInvariant_in_frame P q hg _ (productFrame q hk hs))

/-- Original geometric generators identify the terminating recursion once
the terminal and lower-genus identifications have been discharged. -/
theorem ancestorValue_eq_of_identifications (base : SurfaceAncestorKey X → ℚ)
    (hbase : ∀ q : SurfaceAncestorKey X, q.genus = 2 → q.totalPsi ≤ 1 →
      base q = q.eval Omega P I)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) :
    ancestorValue base q = q.eval Omega P I := by
  symm
  apply ancestorValue_unique base (SurfaceAncestorKey.eval Omega P I)
    (fun r hgen hpsi ↦ (hbase r hgen hpsi).symm) _ q hg
  intro r hgen hpsi
  exact (ancestorStep_eval P T Z F N K hK HF J pS hpS hELS hLBS hUAS hinteriorS hsourceS
    hinS houtS pP hpP hcP hsourceP hinteriorP hinP houtP hzero hone r hgen hpsi).symm

end Geometry
end AxiomaticGW.SurfaceGenusTwo
