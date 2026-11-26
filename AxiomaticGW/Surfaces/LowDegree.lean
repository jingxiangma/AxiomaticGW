/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GetzlerReplay

/-!
# First numerical consequences of checked surface Getzler equations

The graph requests and their complete coefficient checks are fixed independently
of the geometric theory. Their singleton equations imply the stated genus-one
values under the existing geometric laws and finite elliptic seeds. These are
conditional numerical deductions, not constructions of geometric surface theories.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceLowDegree

/-- The plane genus-one line invariant with three point insertions vanishes. -/
theorem genusOne_plane_line {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.plane.blowups)
      SurfaceTarget.plane.Curve SurfaceTarget.plane.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification .plane Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed .plane).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed .plane).query.eval U = -1 / 24)
    (houtput : ∀ i z, z ∈ (GetzlerGraphs.expression i).addMarkings 1 → z.Compatible A F N)
    (p : RelationCertificate.Presentation 1 (Fin 4) 1 33)
    (haccept : GetzlerGraphs.AcceptsExchange p) :
    (SurfaceQuery.points .plane 1 ![1] 3).eval U = 0 := by
  have h := GetzlerGraphs.exchange_checkedPrimaryTerms_eq_zero A I F N H hsource G hcycle
    Omega P T U S Hdiv hpair hH hE 1 houtput ![1] 0 (Option.elim · .point (fun _ ↦ .hyperplane))
    SurfaceGetzlerReplay.planeLine SurfaceGetzlerReplay.planeLine_accepted p haccept
  simp only [SurfaceGetzlerReplay.planeLine, div_one, Multiset.coe_singleton,
    RationalTerms.eval, Multiset.map_singleton, Multiset.sum_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply,
    SurfacePolynomialReduction.variableEval] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- The genus-one two-point invariant of the full class E₁+E₂ vanishes. -/
theorem genusOne_exceptional_sum {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.blowupTwo.blowups)
      SurfaceTarget.blowupTwo.Curve SurfaceTarget.blowupTwo.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification .blowupTwo Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed .blowupTwo).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed .blowupTwo).query.eval U = -1 / 24)
    (houtput : ∀ i z, z ∈ (GetzlerGraphs.expression i).addMarkings 0 → z.Compatible A F N)
    (p : RelationCertificate.Presentation 1 (Fin 4) 1 33)
    (haccept : GetzlerGraphs.AcceptsExchange p) :
    (SurfaceQuery.points .blowupTwo 1 ![1, 1, 0] 2).eval U = 0 := by
  have h := GetzlerGraphs.exchange_checkedPrimaryTerms_eq_zero A I F N H hsource G hcycle
    Omega P T U S Hdiv hpair hH hE 0 houtput ![1, 1, 0] 0 (fun _ ↦ .hyperplane)
    SurfaceGetzlerReplay.exceptionalSum SurfaceGetzlerReplay.exceptionalSum_accepted p haccept
  simp only [SurfaceGetzlerReplay.exceptionalSum, div_one, Multiset.coe_singleton,
    RationalTerms.eval, Multiset.map_singleton, Multiset.sum_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply,
    SurfacePolynomialReduction.variableEval] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

end AxiomaticGW.SurfaceLowDegree
