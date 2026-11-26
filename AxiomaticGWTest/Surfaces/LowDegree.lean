/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.LowDegree
import AxiomaticGWTest.Tautological.GetzlerReplay

/-!
# Checked numerical surface consumers

The original incoming Getzler presentation and the existing finite seed package
suffice for the new deductions. Geometric realization remains an explicit input.
-/

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.LowDegree

open AxiomaticGW

/-- The original certificate gives the plane genus-one line value. -/
example {C : StableCurveCohomology ℚ}
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
    (hseeds : SurfaceSeed.SeedValues U)
    (houtput : ∀ i z, z ∈ (GetzlerGraphs.expression i).addMarkings 1 → z.Compatible A F N) :
    (SurfaceQuery.points .plane 1 ![1] 3).eval U = 0 :=
  SurfaceLowDegree.genusOne_plane_line A I F N H hsource G hcycle Omega P T U S Hdiv hpair
    (hseeds .genusOneHyperplane) (fun i ↦ hseeds (.genusOneExceptional i))
    houtput GetzlerReplay.presentation GetzlerReplay.accepted

/-- The same certificate gives the value in the full exceptional-sum class. -/
example {C : StableCurveCohomology ℚ}
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
    (hseeds : SurfaceSeed.SeedValues U)
    (houtput : ∀ i z, z ∈ (GetzlerGraphs.expression i).addMarkings 0 → z.Compatible A F N) :
    (SurfaceQuery.points .blowupTwo 1 ![1, 1, 0] 2).eval U = 0 :=
  SurfaceLowDegree.genusOne_exceptional_sum A I F N H hsource G hcycle Omega P T U S Hdiv hpair
    (hseeds .genusOneHyperplane) (fun i ↦ hseeds (.genusOneExceptional i))
    houtput GetzlerReplay.presentation GetzlerReplay.accepted

end AxiomaticGWTest.Surfaces.LowDegree
