/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlanePrimaryBenchmarks
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusZeroCompression

open AxiomaticGW SurfaceGenusZero SurfacePolynomialReduction

/-- The frozen plane suite now includes the nontrivial energy-twelve query. -/
example : cachedPointValue .plane ![4] = 620 := plane_primary_values 3

/-- Kernel replay rejects a changed coefficient in the held complete request. -/
example : ¬RationalTerms.Equivalent
    (WDVV.compactPrimaryTerms .plane 8 ![4] (WDVV.reconstructionLabels .plane))
    (RationalTerms.term 1 {pointVariable .plane ![4]} +
      RationalTerms.term (-33) {pointVariable .plane ![1], pointVariable .plane ![3]} +
      RationalTerms.term (-225) {pointVariable .plane ![2], pointVariable .plane ![2]}) := by
  decide +kernel

/-- The accepted polynomial cannot be reused after changing the marking request. -/
example : ¬RationalTerms.Equivalent
    (WDVV.compactPrimaryTerms .plane 7 ![4] (WDVV.reconstructionLabels .plane))
    SurfacePlaneQuartic.terms := by decide +kernel

/-- All four plane queries are geometric positive-class requests, including the unstable line. -/
example (d : Fin 4) : (SurfaceQuery.points .plane 0 ![d.val + 1]
    (3 * (d.val + 1) - 1)).GeometricDomain := by
  fin_cases d <;> decide +kernel

/-- Compression does not identify an F₁ conic with an equal-energy exceptional class. -/
example : ¬RationalTerms.Equivalent
    (WDVV.compactPrimaryTerms .hirzebruchOne 2 ![2, 2]
      (WDVV.reconstructionLabels .hirzebruchOne))
    (WDVV.compactPrimaryTerms .hirzebruchOne 2 ![6, 0]
      (WDVV.reconstructionLabels .hirzebruchOne)) := by decide +kernel

/-- Both exceptional coordinates survive compression on the two-point blowup. -/
example : ¬RationalTerms.Equivalent
    (WDVV.compactPrimaryTerms .blowupTwo 2 ![2, 2, 2]
      (WDVV.reconstructionLabels .blowupTwo))
    (WDVV.compactPrimaryTerms .blowupTwo 2 ![0, 6, 0]
      (WDVV.reconstructionLabels .blowupTwo)) := by decide +kernel

/-- The original Sage-exported WDVV replay certifies the quartic geometric deduction. -/
example {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S) (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.plane.blowups)
      SurfaceTarget.plane.Curve SurfaceTarget.plane.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification .plane Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hline : (SurfaceSeed.line : SurfaceSeed .plane).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N) :
    (SurfaceQuery.points .plane 0 ![4] 11).eval U = 620 := by
  exact plane_primary_benchmark_eq_eval A I F N H hsource hboundary
    WDVVReplay.presentation WDVVReplay.accepted Omega P T U S Hdiv hpair hline houtput 3

end AxiomaticGWTest.Surfaces.GenusZeroCompression
