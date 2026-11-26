/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.L24
public import AxiomaticGW.Surfaces.OnePsiReduction

/-!
# Complete L24 equations in the first-descendant surface variables

Use the same proved substitution as the normalized BP equations. Primary and
first-power ancestors become stable-map descendant families, including the
negative rational-tail correction. Higher powers retain their ancestor tag.
All original L24 columns, constants and full curve classes are preserved.
These equations can be combined with BP in a common variable space; no
invertible system, new seed or completed reconstruction is asserted here.
-/

@[expose] public section

namespace AxiomaticGW.L24Relation
open RelationCertificate PsiBoundaryExpansion

set_option maxRecDepth 20000

/-- Normalize the full L24 equation in the same variable space as BP. -/
def normalizedGenusTwoTerms (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms (SurfacePolynomialReduction.Variable X) :=
  RationalTerms.affineSubstitute SurfacePolynomialReduction.normalizedTerms
    (genusTwoTerms X n beta k a)

/-- The full, uncollected L24 support satisfies the affine substitution precondition. -/
theorem genusTwoTerms_card_le_one (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (t : ℚ × Multiset (SurfaceAncestorKey X)) (ht : t ∈ genusTwoTerms X n beta k a) :
    t.2.card ≤ 1 := by
  rcases ((genusTwoTerms_bound X n beta k a) t ht).affine with hz | ⟨q, hq, _⟩
  · rw [hz, Multiset.card_zero]; omega
  · rw [hq, Multiset.card_singleton]

attribute [local instance] strataRealizationModule

/-- Original class sources and finite low-genus seeds imply the normalized equation.
The extra input is the same primitive cotangent comparison used by normalized BP. -/
theorem eval_normalizedGenusTwoTerms_eq_zero {X : SurfaceTarget}
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
    {V : StableMapIntersection U} {St : StableMapStabilization V}
    (RT : RationalTailIntersection V St P)
    (n : ℕ) (hterms : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (hadded : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms.eval (SurfacePolynomialReduction.variableEval U P)
      (normalizedGenusTwoTerms X n beta k a) = 0 := by
  rw [normalizedGenusTwoTerms, RationalTerms.eval_affineSubstitute
    (SurfacePolynomialReduction.variableEval U P) (SurfaceAncestorKey.eval Omega P I)
    SurfacePolynomialReduction.normalizedTerms
    (SurfacePolynomialReduction.eval_normalizedTerms U P T laws H hpair Z F N J
      hWsource hboundary pW hpW hline hEzero hWoutput RT)
    _ (genusTwoTerms_card_le_one X n beta k a)]
  exact eval_genusTwoTerms_eq_zero_from_geometry U P T laws H hpair Z F N J hWsource hboundary
    pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms
    hline hEzero hH hE hWoutput hGoutput HF hbp hin hout hl hp hs hhigh hs2 hs3 hp2 hp3
    hrational hr4 hr5 hwdvv n hterms hadded beta k a

end AxiomaticGW.L24Relation
