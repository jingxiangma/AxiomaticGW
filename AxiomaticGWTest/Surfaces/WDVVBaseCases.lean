/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlaneGenusZero
import AxiomaticGW.Surfaces.StrictLine
import AxiomaticGWTest.Tautological.WDVVReplay
import AxiomaticGWTest.Tautological.GetzlerReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.WDVVBaseCases

open AxiomaticGW

/-- The repeated line invariant is a square, not a single occurrence. -/
example : ¬ RationalTerms.Equivalent SurfacePlaneGenusZero.conicTerms
    (RationalTerms.term 1 {.inr (SurfaceQuery.points .plane 0 ![2] 5)} +
      RationalTerms.term (-1) {.inr (SurfaceQuery.points .plane 0 ![1] 2)}) := by
  decide +kernel

/-- A candidate for two additional markings cannot certify a one-marking request. -/
example : ¬ RationalTerms.Equivalent
    (WDVV.primaryTerms .plane 1 ![2] 0
      (Option.elim · .point ![.hyperplane, .hyperplane, .point, .point]))
    SurfacePlaneGenusZero.conicTerms := by decide +kernel

section Plane

/-- The original replay and finite seed package give the conic value. -/
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
    (hpair : T.DivisorPairingCompatible Adiv) (hseeds : SurfaceSeed.SeedValues U)
    (houtput : ∀ i z, z ∈ (WDVV.expression i).addMarkings 2 → z.Compatible A F N) :
    (SurfaceQuery.points .plane 0 ![2] 5).eval U = 1 :=
  SurfacePlaneGenusZero.conic A I F N H hsource hboundary Omega P T U S Hdiv hpair
    (hseeds .line) houtput WDVVReplay.presentation WDVVReplay.accepted

end Plane

section Hirzebruch

/-- The F₁ consumer needs no genus-one seed or genus-one relation. -/
example {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S) (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.hirzebruchOne.blowups)
      SurfaceTarget.hirzebruchOne.Curve SurfaceTarget.hirzebruchOne.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification .hirzebruchOne Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hline : (SurfaceSeed.line : SurfaceSeed .hirzebruchOne).query.eval U = 1)
    (hE : (SurfaceSeed.exceptional 0 : SurfaceSeed .hirzebruchOne).query.eval U = 1) :
    (SurfaceQuery.points .hirzebruchOne 0 ![0, 1] 1).eval U = 1 :=
  SurfaceBlowupGenusZero.hirzebruch_fiber A I F N H hsource hboundary
    WDVVReplay.presentation WDVVReplay.accepted Omega P T U S Hdiv hpair hline hE

end Hirzebruch

section StrictLine

/-- Both original certificates and the unchanged finite seeds determine L. -/
example {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S) (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hWsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.blowupTwo.blowups)
      SurfaceTarget.blowupTwo.Curve SurfaceTarget.blowupTwo.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification .blowupTwo Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv) (hseeds : SurfaceSeed.SeedValues U) :
    (SurfaceQuery.points .blowupTwo 0 ![0, 0, 2] 1).eval U = 0 ∧
      (SurfaceQuery.points .blowupTwo 1 ![0, 0, 2] 2).eval U = 0 ∧
      (SurfaceQuery.points .blowupTwo 1 ![0, 0, 1] 1).eval U = 0 :=
  SurfaceStrictLine.baseCases A I F N H hWsource hboundary WDVVReplay.presentation
    WDVVReplay.accepted hGsource G hcycle GetzlerReplay.presentation GetzlerReplay.accepted
    Omega P T U S Hdiv hpair (hseeds .line) (fun i ↦ hseeds (.exceptional i))
    (hseeds .genusOneHyperplane) (fun i ↦ hseeds (.genusOneExceptional i))

end StrictLine

end AxiomaticGWTest.Surfaces.WDVVBaseCases
