/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.L24Terms
public import AxiomaticGW.Tautological.L24GW

/-!
# Complete L24 equations on the three fixed surfaces

All 721 original nonzero columns and their signed decorated pullbacks use the
existing exact surface contraction. Reconstructed genera zero and one leave
an affine system of actual genus-two ancestor variables, with full effective
class remainders. Original geometric sources and finite low-genus seeds give
soundness; no genus-two value, invertible pivot or reconstruction oracle is added.
-/

@[expose] public section

namespace AxiomaticGW.L24Relation
open GluingExpression RelationCertificate PsiBoundaryExpansion

-- The finite source uses the same reduction depth as its checked graph frame.
set_option maxRecDepth 20000

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- The original L24 sources imply the complete surface equation after the existing
lower-genus soundness identifications. The remaining variables are actual ancestors. -/
theorem eval_genusTwoTerms_eq_zero
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hbp : (A 2 (Fin 3)).map BelorousskiPandharipande.paperRelation = 0)
    (hin : ∀ t ∈ L24Initial.bp, t.2.expression.Compatible A F N ∧
      t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ L24Initial.bp, ∀ z ∈ t.2.addMarkings 1,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (hl : (A 2 (ExtraMarkings 1 (Fin 3))).RelabelCompatible (A 2 (Fin 4))
      (BelorousskiPandharipande.stableArity.extraMarkings 1) L24Symmetry.stableArity
      L24Initial.labels)
    (hp : (A 2 (Fin 4)).LegPsiCompatible P L24Symmetry.stableArity)
    (hs : ∀ p, (A 2 (Fin 4)).RelabelCompatible (A 2 (Fin 4))
      L24Symmetry.stableArity L24Symmetry.stableArity (L24Symmetry.labels p))
    (hhigh : L24HighPsi.Compatible A F P)
    (hs2 : (A 2 (Fin 2)).map GenusTwoPsiPullbacks.squareTwo.strata = 0)
    (hs3 : (A 2 (Fin 3)).map GenusTwoPsiPullbacks.squareThree.strata = 0)
    (hp2 : (A 2 (Fin 2)).map GenusTwoPsiProduct.cotangentRelation.strata = 0)
    (hp3 : (A 2 (Fin 3)).map GenusTwoPsiPullbacks.productThree.strata = 0)
    (hrational : L24RationalPsi.Compatible A F P)
    (hr4 : (A 0 (Fin 4)).map (interpret (RationalPsiRelation.columns 1)
      (RationalPsiRelation.coordinates 1)) = 0)
    (hr5 : (A 0 (Fin 5)).map (interpret (RationalPsiRelation.columns 2)
      (RationalPsiRelation.coordinates 2)) = 0)
    (hwdvv : L24WDVV.Compatible A F P)
    (hwsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hwboundary : WDVV.BoundaryClassesEqual F)
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (hone : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
      SurfaceGenusOne.ancestorValue X q = q.eval Omega P I)
    (n : ℕ) (hterms : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P)
    (hadded : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I) (genusTwoTerms X n beta k a) = 0 := by
  have he := gw_forget_relation_from_geometry A F N Omega P K hK H G hbp hin hout hl hp hs
    hhigh hs2 hs3 hp2 hp3 hrational hr4 hr5 hwdvv hwsource hwboundary n hterms hadded
    beta k (fun s ↦ (a s).value)
  rw [genusTwoTerms, eval_surfaceTerms]
  simp only [SurfaceGenusTwo.vertexTerms, SurfaceGenusTwo.eval_residualTerms P T hzero hone,
    SurfaceAncestorKey.eval_ofLabels,
    GluingExpression.surfaceDecoratedEval_eq_gwDecoratedAncestorContraction Omega P I
      T.pairing_eq, Algebra.algebraMap_self_apply]
  simpa only [CotangentCombination.gwContraction, Rat.smul_def, Rat.cast_id] using he

/-- Full surface L24 soundness from the named geometric laws and unchanged finite
low-genus seeds. Both component algorithms are identified by their existing theorems. -/
theorem eval_genusTwoTerms_eq_zero_from_geometry {X : SurfaceTarget}
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (J : GluingForgetfulCompatibility F N)
    (hWsource : ∀ i, (WDVV.expression i).Compatible Z F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (pW : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hpW : WDVV.AcceptsExchange pW)
    (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible Z F N)
    (GG : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (Z 1 (Fin 4)).map (GetzlerGraphs.cycle x) = GG.cycle x)
    (pG : RelationCertificate.Presentation 1 (Fin 4) 1 33)
    (hpG : GetzlerGraphs.AcceptsExchange pG)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (pPsi : RelationCertificate.Presentation 1 (Fin 1) 2 3)
    (hpPsi : GenusOnePsi.AcceptsExchange pPsi)
    (hpsi : (Z 1 (Fin 1)).LegPsiCompatible P GenusOnePsi.stableArity)
    (hfund : (Z 1 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Fin 1) GenusOnePsi.stableArity)) = 1)
    (hrows : ∀ i, (Z 1 (Fin 1)).map
      (RelationCertificate.interpret GenusOnePsi.columns (GenusOnePsi.rows i)) = 0)
    (hloop : GenusOnePsi.loopExpression.Compatible Z F N)
    (hzeroTerms : ∀ n t, t ∈ PsiBoundaryExpansion.genusZeroTerms 0 n → t.2.Compatible Z F N)
    (honeTerms : ∀ n t, t ∈ PsiBoundaryExpansion.genusOneTerms n → t.2.Compatible Z F N)
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hEzero : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible Z F N)
    (HF : TailForgetCompatible C)
    (hbp : (Z 2 (Fin 3)).map BelorousskiPandharipande.paperRelation = 0)
    (hin : ∀ t ∈ L24Initial.bp, t.2.expression.Compatible Z F N ∧
      t.2.expression.CotangentCompatible Z P)
    (hout : ∀ t ∈ L24Initial.bp, ∀ z ∈ t.2.addMarkings 1,
      z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
    (hl : (Z 2 (ExtraMarkings 1 (Fin 3))).RelabelCompatible (Z 2 (Fin 4))
      (BelorousskiPandharipande.stableArity.extraMarkings 1) L24Symmetry.stableArity
      L24Initial.labels)
    (hp : (Z 2 (Fin 4)).LegPsiCompatible P L24Symmetry.stableArity)
    (hs : ∀ p, (Z 2 (Fin 4)).RelabelCompatible (Z 2 (Fin 4))
      L24Symmetry.stableArity L24Symmetry.stableArity (L24Symmetry.labels p))
    (hhigh : L24HighPsi.Compatible Z F P)
    (hs2 : (Z 2 (Fin 2)).map GenusTwoPsiPullbacks.squareTwo.strata = 0)
    (hs3 : (Z 2 (Fin 3)).map GenusTwoPsiPullbacks.squareThree.strata = 0)
    (hp2 : (Z 2 (Fin 2)).map GenusTwoPsiProduct.cotangentRelation.strata = 0)
    (hp3 : (Z 2 (Fin 3)).map GenusTwoPsiPullbacks.productThree.strata = 0)
    (hrational : L24RationalPsi.Compatible Z F P)
    (hr4 : (Z 0 (Fin 4)).map (interpret (RationalPsiRelation.columns 1)
      (RationalPsiRelation.coordinates 1)) = 0)
    (hr5 : (Z 0 (Fin 5)).map (interpret (RationalPsiRelation.columns 2)
      (RationalPsiRelation.coordinates 2)) = 0)
    (hwdvv : L24WDVV.Compatible Z F P)
    (n : ℕ) (hterms : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (hadded : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I) (genusTwoTerms X n beta k a) = 0 := by
  exact eval_genusTwoTerms_eq_zero Z F N Omega P T K hK HF J hbp hin hout hl hp hs
    hhigh hs2 hs3 hp2 hp3 hrational hr4 hr5 hwdvv hWsource hboundary
    (SurfaceGenusZero.ancestorValue_eq_eval U T laws H hpair Z F N J hWsource hboundary pW hpW
      P K hK hzeroTerms hline hEzero hWoutput)
    (SurfaceGenusOne.ancestorValue_eq_eval U P T laws H hpair Z F N J hWsource hboundary pW hpW
      hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms
      hline hEzero hH hE hWoutput hGoutput) n hterms hadded beta k a

end AxiomaticGW.L24Relation
