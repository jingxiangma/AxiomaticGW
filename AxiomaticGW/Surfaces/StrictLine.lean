/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.BlowupGenusZero
public import AxiomaticGW.Surfaces.Fixtures.StrictLineGetzler

/-!
# The genus-one base case for L = H−E₁−E₂

The genus-zero normalization of L is derived by WDVV from the existing line
and exceptional seeds. Three complete Getzler equations in class 2L then
give the genus-one one-point vanishing for L and both double-class vanishings.
The argument keeps L distinct from E₁ and E₂ throughout.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceStrictLine

/-- The original WDVV and Getzler certificates determine the L base cases.
No L-class value or support-vanishing assertion is added to the seed package. -/
theorem baseCases {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hWsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (pW : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hpW : WDVV.AcceptsExchange pW)
    (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
    (pG : RelationCertificate.Presentation 1 (Fin 4) 1 33)
    (hpG : GetzlerGraphs.AcceptsExchange pG)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.blowupTwo.blowups)
      SurfaceTarget.blowupTwo.Curve SurfaceTarget.blowupTwo.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification .blowupTwo Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hline : (SurfaceSeed.line : SurfaceSeed .blowupTwo).query.eval U = 1)
    (hEzero : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed .blowupTwo).query.eval U = 1)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed .blowupTwo).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed .blowupTwo).query.eval U =
      -1 / 24) :
    (SurfaceQuery.points .blowupTwo 0 ![0, 0, 2] 1).eval U = 0 ∧
      (SurfaceQuery.points .blowupTwo 1 ![0, 0, 2] 2).eval U = 0 ∧
      (SurfaceQuery.points .blowupTwo 1 ![0, 0, 1] 1).eval U = 0 := by
  have hL := (SurfaceBlowupGenusZero.blowup_baseCases A I F N H hWsource hboundary pW hpW
    Omega P T U S Hdiv hpair hline hEzero).1
  have houtput : ∀ i z, z ∈ (GetzlerGraphs.expression i).addMarkings 0 →
      z.Compatible A F N := by
    intro i z hz
    simp only [GluingExpression.addMarkings, List.mem_singleton] at hz
    subst z
    exact hGsource i
  have h4 := GetzlerGraphs.exchange_checkedPrimaryTerms_eq_zero A I F N H hGsource G hcycle
    Omega P T U S Hdiv hpair hH hE 0 houtput ![0, 0, 2] 0 (fun _ ↦ .hyperplane)
    (SurfaceStrictLineGetzler.terms 24 (-5) (-9))
    SurfaceStrictLineGetzler.hyperplane_accepted pG hpG
  have h3 := GetzlerGraphs.exchange_checkedPrimaryTerms_eq_zero A I F N H hGsource G hcycle
    Omega P T U S Hdiv hpair hH hE 0 houtput ![0, 0, 2] 0
    ![.hyperplane, .hyperplane, .hyperplane, .exceptional 0]
    (SurfaceStrictLineGetzler.terms 15 (-11 / 2) 0)
    SurfaceStrictLineGetzler.threeHyperplanes_accepted pG hpG
  have h1 := GetzlerGraphs.exchange_checkedPrimaryTerms_eq_zero A I F N H hGsource G hcycle
    Omega P T U S Hdiv hpair hH hE 0 houtput ![0, 0, 2] 0
    ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0]
    (SurfaceStrictLineGetzler.terms (-3) (-13 / 2) 0)
    SurfaceStrictLineGetzler.oneHyperplane_accepted pG hpG
  simp only [SurfaceStrictLineGetzler.terms, RationalTerms.eval_add, RationalTerms.eval_term,
    Multiset.map_coe, Multiset.prod_coe, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Multiset.map_singleton, Multiset.prod_singleton,
    Algebra.algebraMap_self_apply, SurfacePolynomialReduction.variableEval,
    hL, one_mul, mul_one, zero_mul, add_zero] at h4 h3 h1
  have hy : (SurfaceQuery.points .blowupTwo 0 ![0, 0, 2] 1).eval U = 0 := by linarith
  have hx : (SurfaceQuery.points .blowupTwo 1 ![0, 0, 1] 1).eval U = 0 := by linarith
  refine ⟨hy, ?_, hx⟩
  linarith

end AxiomaticGW.SurfaceStrictLine
