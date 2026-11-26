/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusTwoNormalizedBP
public import AxiomaticGW.Surfaces.ExceptionalEvaluationSupport

/-!
# The degree-zero genus-two primary point on F₁

The complete exceptional BP equation relates the class-zero primary point,
the audited class-zero exceptional first descendant, and two point-supported
positive exceptional descendants. The class-level exceptional evaluation
support removes the latter two. The existing divisor seed then cancels the
constant and determines the primary point to be zero.

The final theorem derives the original equation from its source relations
and primitive geometry. Neither the primary value nor a solved recurrence
is assumed. The new evaluation-support condition remains a named geometric
input; its geometric construction is not supplied here.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open BelorousskiPandharipande RelationCertificate PsiBoundaryExpansion
local notation "X" => SurfaceTarget.hirzebruchOne
attribute [local instance] strataRealizationModule

/-- The compact exceptional equation is the full normalized BP contraction,
including its constant and signed rational-tail corrections. -/
theorem hirzebruchOne_exceptional_equation (v : SurfacePolynomialReduction.Variable X → ℚ) :
    RationalTerms.eval v (normalizedGenusTwoTerms X 0 ![1, 0] 0
      (fun _ ↦ .exceptional 0)) =
      RationalTerms.eval v SurfaceGenusTwoNormalizedBP.exceptional := by
  rw [normalizedGenusTwoTerms, RationalTerms.eval_affineSubstitute_eq_of_equivalent v
    SurfacePolynomialReduction.normalizedTerms _ _ SurfaceGenusTwoBP.exceptional_checked
    (genusTwoTerms_card_le_one _ _ _ _ _) (by decide +kernel)]
  exact RationalTerms.eval_eq_of_equivalent v _ _
    SurfaceGenusTwoNormalizedBP.exceptional_normalized

/-- The exact BP equation, exceptional evaluation support and the existing
class-zero divisor seed determine the primary point; no primary seed is needed. -/
theorem hirzebruchOne_zero_primary_of_equation
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.hirzebruchOne.blowups)
      SurfaceTarget.hirzebruchOne.Curve SurfaceTarget.hirzebruchOne.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (V : StableMapIntersection U) (hV : ExceptionalPointSupport V)
    (hEtwo : (SurfaceSeed.genusTwoExceptional 0 : SurfaceSeed X).query.eval U = -1 / 2880)
    (heq : RationalTerms.eval (SurfacePolynomialReduction.variableEval U P)
      (normalizedGenusTwoTerms X 0 ![1, 0] 0 (fun _ ↦ .exceptional 0)) = 0) :
    (SurfaceQuery.points X 2 0 1).eval U = 0 := by
  have hb : (![1, 0] : SurfaceTarget.hirzebruchOne.Curve) ≠ 0 := by decide +kernel
  have hd : SurfaceTarget.hirzebruchOne.divisorIntersections
      (![1, 0] : SurfaceTarget.hirzebruchOne.Curve) 0 = 0 := by decide +kernel
  have hK : (SurfaceFirstDescendant.query 2 (![1, 0] : SurfaceTarget.hirzebruchOne.Curve)
      (.exceptional 0) 1).eval U = 0 :=
    exceptional_first_divisor_eval_eq_zero V hV ![1, 0] hb hd (.exceptional 0)
  have hP : (SurfaceFirstDescendant.query 2 (![1, 0] : SurfaceTarget.hirzebruchOne.Curve)
      .point 0).eval U = 0 :=
    exceptional_first_point_eval_eq_zero V hV ![1, 0] hb hd
  have hKzero : (SurfaceFirstDescendant.query 2 (0 : SurfaceTarget.hirzebruchOne.Curve)
      (.exceptional 0) 0).eval U = -1 / 2880 := hEtwo
  rw [hirzebruchOne_exceptional_equation] at heq
  simp only [SurfaceGenusTwoNormalizedBP.exceptional, RationalTerms.eval_add,
    RationalTerms.eval_term, Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply, mul_one,
    SurfacePolynomialReduction.variableEval] at heq
  rw [hKzero, hK, hP] at heq
  linarith

/-- F₁'s degree-zero primary point follows from the original BP source
geometry, finite low-genus seeds, the audited exceptional divisor seed and
class-level exceptional evaluation support. -/
theorem hirzebruchOne_zero_primary
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.hirzebruchOne.blowups)
      SurfaceTarget.hirzebruchOne.Curve SurfaceTarget.hirzebruchOne.effective C}
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
    (hEtwo : (SurfaceSeed.genusTwoExceptional 0 : SurfaceSeed X).query.eval U = -1 / 2880)
    (hV : ExceptionalPointSupport V) :
    (SurfaceQuery.points X 2 0 1).eval U = 0 := by
  have heq := eval_normalizedGenusTwoTerms_eq_zero U P T laws H hpair Z F N J hWsource
    hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop
    hzeroTerms honeTerms hline hEzero hH hE hWoutput hGoutput HF pB hpB hlB hcB
    hinterior hsource hglue hcotangent RT 0 hout ![1, 0] 0 (fun _ ↦ .exceptional 0)
  exact hirzebruchOne_zero_primary_of_equation U P V hV hEtwo heq

end AxiomaticGW.SurfaceGenusTwo
