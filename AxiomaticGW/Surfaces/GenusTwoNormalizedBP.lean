/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.BelorousskiPandharipande
public import AxiomaticGW.Surfaces.OnePsiReduction

/-!
# BP equations in the canonical first-descendant surface families

Normalize the already proved affine genus-two equation, including the
negative rational-tail correction. Primary and first-power ancestors become
stable-map descendants with only primary point insertions. Other powers
remain tagged ancestors; arbitrary additional marking/power data are still
accepted without asserting that BP alone determines the remaining system.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open RelationCertificate PsiBoundaryExpansion

/-- Exact substitution in the original twenty-term, six-assignment BP expansion. -/
def normalizedGenusTwoTerms (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) :
    RationalTerms (SurfacePolynomialReduction.Variable X) :=
  RationalTerms.affineSubstitute SurfacePolynomialReduction.normalizedTerms
    (genusTwoTerms X n beta k a)

theorem genusTwoTerms_card_le_one (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    (t : ℚ × Multiset (SurfaceAncestorKey X)) (ht : t ∈ genusTwoTerms X n beta k a) :
    t.2.card ≤ 1 := by
  rcases ((genusTwoTerms_bound X n beta k a) t ht).affine with hz | ⟨q, hq, _⟩
  · rw [hz, Multiset.card_zero]; omega
  · rw [hq, Multiset.card_singleton]

attribute [local instance] strataRealizationModule

/-- The normalized equation follows from the same source relations and
finite low-genus seeds, plus the primitive rational-tail cotangent law.
No pivot, genus-two value or recurrence is assumed. -/
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
    (n : ℕ) (hout : ∀ i e t, t ∈ (orbitCotangentTerm i e).addMarkings n →
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 3) → ℕ)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) :
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
    hline hEzero hH hE hWoutput hGoutput HF pB hpB hlB hcB hinterior hsource hglue hcotangent
    n hout beta k a

end AxiomaticGW.BelorousskiPandharipande
