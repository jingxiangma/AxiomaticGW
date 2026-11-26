/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusTwoNormalizedBP

/-!
# Two derived genus-two values on the two-point blowup

The original BP geometry, reconstructed lower genera, cotangent comparison
and the already specified finite genus-two divisor seeds imply the
class-zero primary point value and a cross-exceptional first descendant.
Neither value is added as an independent seed or assumed recurrence.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open BelorousskiPandharipande RelationCertificate PsiBoundaryExpansion
local notation "X" => SurfaceTarget.blowupTwo
attribute [local instance] strataRealizationModule

/-- Derived initial values, conditional only on the original source geometry,
primitive GW laws and the unchanged finite seed package. -/
theorem blowupTwo_initialValues
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.blowupTwo.blowups)
      SurfaceTarget.blowupTwo.Curve SurfaceTarget.blowupTwo.effective C}
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
    (pB : Exchange) (hpB : AcceptsExchange pB)
    (hlB : ∀ e, (Z 2 (Fin 3)).RelabelCompatible (Z 2 (Fin 3))
      stableArity stableArity (labelPermutation e))
    (hcB : ∀ b, SourceMapCompatible Z F b)
    (hinterior : ∀ i : Fin 4, (Z 2 (Fin 3)).map
      (interpret columns (unsymmetrizedRows (Fin.castAdd 16 i))) = 0)
    (hsource : ∀ i, (Z (sourceGenus (sourceFamily i)) (Fin (sourceArity (sourceFamily i)))).map
      (sourceExpression i) = 0)
    (hglue : ∀ i e, (orbitTerm i e).1.Compatible Z F N)
    (hcotangent : ∀ i e, (orbitTerm i e).1.CotangentCompatible Z P)
    {V : StableMapIntersection U} {St : StableMapStabilization V}
    (RT : RationalTailIntersection V St P)
    (hout : ∀ i e t, t ∈ (orbitCotangentTerm i e).addMarkings 0 →
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
    (hEtwo : ∀ i, (SurfaceSeed.genusTwoExceptional i : SurfaceSeed X).query.eval U = -1 / 2880) :
    (SurfaceQuery.points X 2 0 1).eval U = 0 ∧
      (SurfaceFirstDescendant.query 2 ![0,1,0] (.exceptional 0) 1).eval U = 0 := by
  have hzero := eval_normalizedGenusTwoTerms_eq_zero U P T laws H hpair Z F N J hWsource
    hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop
    hzeroTerms honeTerms hline hEzero hH hE hWoutput hGoutput HF pB hpB hlB hcB
    hinterior hsource hglue hcotangent RT 0 hout ![0,0,1] 0
    ![.exceptional 0, .exceptional 1, .hyperplane]
  have hcross := eval_normalizedGenusTwoTerms_eq_zero U P T laws H hpair Z F N J hWsource
    hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop
    hzeroTerms honeTerms hline hEzero hH hE hWoutput hGoutput HF pB hpB hlB hcB
    hinterior hsource hglue hcotangent RT 0 hout ![0,1,0] 0 (fun _ ↦ .exceptional 0)
  rw [SurfaceGenusTwoNormalizedBP.eval_blowupTwoLine] at hzero
  rw [SurfaceGenusTwoNormalizedBP.eval_distinctExceptional] at hcross
  simp only [SurfaceGenusTwoNormalizedBP.blowupTwoLine, RationalTerms.eval_add,
    RationalTerms.eval_term, Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply, mul_one,
    SurfacePolynomialReduction.variableEval] at hzero
  have hH' : (SurfaceFirstDescendant.query 2 (0 : SurfaceTarget.blowupTwo.Curve)
      .hyperplane 0).eval U = -1 / 960 :=
    hHtwo
  have hE' (i : Fin SurfaceTarget.blowupTwo.blowups) :
      (SurfaceFirstDescendant.query 2 (0 : SurfaceTarget.blowupTwo.Curve)
        (.exceptional i) 0).eval U = -1 / 2880 :=
    hEtwo i
  rw [hH', hE', hE'] at hzero
  simp only [SurfaceGenusTwoNormalizedBP.distinctExceptional, RationalTerms.eval_term,
    Multiset.map_singleton, Multiset.prod_singleton, Algebra.algebraMap_self_apply,
    SurfacePolynomialReduction.variableEval] at hcross
  constructor <;> linarith

end AxiomaticGW.SurfaceGenusTwo
