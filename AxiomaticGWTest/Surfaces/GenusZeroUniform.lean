/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusZeroUniform
import AxiomaticGW.Surfaces.PlaneGenusZero
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusZeroUniform

open AxiomaticGW SurfaceGenusZero SurfacePolynomialReduction

/-- The unmarked degree-zero tree need not vanish, so marking vanishing is not vacuous. -/
example : constantCoefficient (WDVV.expression 0)
    (![.unit, .unit, .hyperplane, .hyperplane] : Fin 4 → SurfaceBasisLabel .plane) = 1 := by
  decide +kernel

/-- Every placement of the added point has zero degree-zero constant contribution. -/
example : (((WDVV.expression 0).addMarkings 1).map fun z ↦
    constantCoefficient z (pointLabels
      (![.unit, .unit, .hyperplane, .hyperplane] :
        Fin 4 → SurfaceBasisLabel .plane) 1)).sum = 0 := by
  decide +kernel

/-- The compact computation agrees with the earlier placement evaluator on a divisor profile. -/
example : WDVV.pointMarkedCoefficient .blowupTwo 2 ![2, 1, 2]
      ![.hyperplane, .point, .exceptional 0, .exceptional 0] =
    WDVV.primaryPointCoefficient .blowupTwo 2 ![2, 1, 2]
      (pointLabels ![.hyperplane, .point, .exceptional 0, .exceptional 0] 2) := by
  decide +kernel

/-- Hyperplane intersection zero does not destroy this pivot on a multiple exceptional class. -/
example : WDVV.pointMarkedCoefficient .hirzebruchOne 0 ![4, 0]
    (WDVV.reconstructionLabels .hirzebruchOne) = 1 := by decide +kernel

/-- All three curve coordinates are retained at the energy-twelve benchmark boundary. -/
example : WDVV.pointMarkedCoefficient .blowupTwo 8 ![4, 4, 4]
    (WDVV.reconstructionLabels .blowupTwo) = 1 := by decide +kernel

/-- A large marking count does not make the compact computation enumerate its placements. -/
example : WDVV.pointMarkedCoefficient .plane 296 ![100]
    (WDVV.reconstructionLabels .plane) = 1 := by decide +kernel

/-- The same large request is certified against the original expansion without evaluating it. -/
example : RationalTerms.coefficient
    (WDVV.primaryTerms .plane 296 ![100] 0
      (pointLabels (WDVV.reconstructionLabels .plane) 296))
    {pointVariable .plane ![100]} = 1 :=
  WDVV.primaryTerms_reconstruction_coefficient .plane ![100] (by decide +kernel)

/-- A missing point fails the dimension equation. -/
example : WDVV.pointMarkedCoefficient .plane 1 ![2]
    (WDVV.reconstructionLabels .plane) = 0 := by decide +kernel

/-- The energy-four threshold is necessary for the hyperplane/point profile. -/
example : WDVV.pointMarkedCoefficient .blowupTwo 0 ![0, 3, 0]
    (WDVV.reconstructionLabels .blowupTwo) = 0 := by decide +kernel

/-- The finite energy-three cover contains two F₁ classes. -/
example : ((SurfaceTarget.hirzebruchOne.bounded 3).filter
    (fun beta ↦ SurfaceTarget.hirzebruchOne.effective.energy beta = 3)).card = 2 := by
  decide +kernel

/-- The finite energy-three cover contains all ten two-point-blowup classes. -/
example : ((SurfaceTarget.blowupTwo.bounded 3).filter
    (fun beta ↦ SurfaceTarget.blowupTwo.effective.energy beta = 3)).card = 10 := by
  decide +kernel

/-- Selecting E₂ is essential when the E₁ coordinate vanishes. -/
example : WDVV.pointMarkedCoefficient .blowupTwo 0 ![0, 3, 0]
    (WDVV.blowupEnergyThreeLabels ![0, 3, 0]) = -3 := by decide +kernel

/-- The F₁ selector covers both the exceptional and positive plane-degree branches. -/
example : WDVV.pointMarkedCoefficient .hirzebruchOne 0 ![3, 0]
      (WDVV.hirzebruchEnergyThreeLabels ![3, 0]) = -3 ∧
    WDVV.pointMarkedCoefficient .hirzebruchOne 0 ![1, 1]
      (WDVV.hirzebruchEnergyThreeLabels ![1, 1]) = -1 := by decide +kernel

private theorem conicLower : RationalTerms.Equivalent
    (lowerTerms .plane ![2] (WDVV.primaryTerms .plane 2 ![2] 0
      (pointLabels (WDVV.reconstructionLabels .plane) 2)))
    (RationalTerms.term (-1) (Multiset.replicate 2 (pointVariable .plane ![1]))) := by
  decide +kernel

/-- The uniform step recovers the conic using the original relation and line seed,
with no separate coefficient certificate supplied by the caller. -/
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
    (houtput : ∀ i z, z ∈ (WDVV.expression i).addMarkings 2 → z.Compatible A F N) :
    (SurfaceQuery.points .plane 0 ![2] 5).eval U = 1 := by
  have h := WDVV.primary_point_eq_reconstruction A I F N H hsource hboundary Omega P T U S
    Hdiv hpair ![2] (by decide +kernel) houtput WDVVReplay.presentation WDVVReplay.accepted
  rw [show SurfaceTarget.plane.effective.energy ![2] - 4 = 2 from by decide +kernel] at h
  rw [RationalTerms.eval_eq_of_equivalent _ _ _ conicLower] at h
  rw [show SurfaceTarget.plane.effective.energy ![2] - 1 = 5 from by decide +kernel] at h
  have hseed : variableEval U P (pointVariable .plane ![1]) = 1 := by
    change (SurfaceQuery.points .plane 0 SurfaceTarget.plane.lineCurve 2).eval U = 1 at hline
    rw [show SurfaceTarget.plane.lineCurve = ![1] from by decide +kernel] at hline
    exact hline
  simpa only [RationalTerms.eval_term, Algebra.algebraMap_self_apply,
    Multiset.map_replicate, Multiset.prod_replicate, hseed, one_pow, mul_one,
    neg_neg] using h

end AxiomaticGWTest.Surfaces.GenusZeroUniform
