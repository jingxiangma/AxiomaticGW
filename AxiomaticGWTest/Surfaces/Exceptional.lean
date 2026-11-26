/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.Exceptional
import AxiomaticGWTest.Tautological.GetzlerReplay

/-!
# Exceptional reconstruction consumers

The finite seed package and original incoming Getzler certificate supply all
numerical inputs. The two negative checks protect the sign and full class of
the new equations; geometric applicability remains an explicit hypothesis.
-/

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.Exceptional

open AxiomaticGW

example : ¬ RationalTerms.Equivalent
    (SurfaceExceptionalGetzler.hyperplaneTerms .hirzebruchOne 0)
    (RationalTerms.term 9 {.inr (SurfaceQuery.points .hirzebruchOne 1 ![2, 0] 2)}) := by
  decide +kernel

example : ¬ RationalTerms.Equivalent
    (SurfaceExceptionalGetzler.twoHyperplaneTerms .blowupTwo 0)
    (SurfaceExceptionalGetzler.twoHyperplaneTerms .blowupTwo 1) := by
  decide +kernel

/-- Every exceptional divisor of the two fixed blowups uses only existing seeds. -/
example {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hseeds : SurfaceSeed.SeedValues U) (i : Fin X.blowups) :
    (SurfaceQuery.points X 0 (2 • X.exceptionalCurve i) 1).eval U = 0 ∧
      (SurfaceQuery.points X 1 (2 • X.exceptionalCurve i) 2).eval U = 0 ∧
      (SurfaceQuery.points X 1 (X.exceptionalCurve i) 1).eval U = 0 := by
  exact ⟨SurfaceExceptional.genusZero_doubleExceptional A I F N H hsource G hcycle
    Omega P T U S Hdiv hpair (hseeds .genusOneHyperplane)
    (fun j ↦ hseeds (.genusOneExceptional j)) GetzlerReplay.presentation GetzlerReplay.accepted i,
    SurfaceExceptional.genusOne_doubleExceptional A I F N H hsource G hcycle
      Omega P T U S Hdiv hpair (hseeds .genusOneHyperplane)
      (fun j ↦ hseeds (.genusOneExceptional j)) GetzlerReplay.presentation GetzlerReplay.accepted i,
    SurfaceExceptional.genusOne_exceptional A I F N H hsource G hcycle
      Omega P T U S Hdiv hpair (hseeds .genusOneHyperplane)
      (fun j ↦ hseeds (.genusOneExceptional j)) GetzlerReplay.presentation GetzlerReplay.accepted i
      (hseeds (.exceptional i))⟩

end AxiomaticGWTest.Surfaces.Exceptional
