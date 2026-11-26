/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusZeroStep
import AxiomaticGW.Surfaces.PlaneGenusZero
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusZeroStep

open AxiomaticGW SurfaceGenusZero SurfacePolynomialReduction

/-- Equal energy cannot replace equality of the full exceptional curve coordinates. -/
example : ¬ PointMonomial (![1, 0, 0] : SurfaceTarget.blowupTwo.Curve)
    {pointVariable .blowupTwo ![0, 1, 0]} := by
  intro h
  have heq := h.2
  change (![0, 1, 0] : SurfaceTarget.blowupTwo.Curve) = ![1, 0, 0] at heq
  have hcoord := congrFun heq 0
  change (0 : ℕ) = 1 at hcoord
  exact Nat.zero_ne_one hcoord

/-- A squared copy of the original query cannot hide among homogeneous terms. -/
example (X : SurfaceTarget) (beta : X.Curve) :
    ¬ PointMonomial beta (Multiset.replicate 2 (pointVariable X beta)) := by
  intro h
  have hs := h.singleton_of_energy_eq (pointVariable X beta)
    (Multiset.mem_replicate.mpr ⟨by decide, rfl⟩) rfl
  have hc := congrArg Multiset.card hs
  simp only [Multiset.card_replicate, Multiset.card_singleton] at hc
  omega

/-- The fibre/exceptional splitting retains a positive-degree zero-point query. -/
example : RationalTerms.Equivalent
    (lowerTerms .hirzebruchOne ![1, 1]
      (WDVV.primaryTerms .hirzebruchOne 0 ![1, 1] 0
        ![.hyperplane, .point, .exceptional 0, .exceptional 0]))
    (RationalTerms.term 1
      (↑([pointVariable .hirzebruchOne ![0, 1], pointVariable .hirzebruchOne ![1, 0]] :
        List (Variable .hirzebruchOne)) : Multiset (Variable .hirzebruchOne))) := by
  decide +kernel

private theorem conicPivot : RationalTerms.coefficient
    (WDVV.primaryTerms .plane 2 ![2] 0 SurfacePlaneGenusZero.conicLabels)
    {pointVariable .plane ![2]} = 1 := by decide +kernel

private theorem conicLower : RationalTerms.Equivalent
    (lowerTerms .plane ![2]
      (WDVV.primaryTerms .plane 2 ![2] 0 SurfacePlaneGenusZero.conicLabels))
    (RationalTerms.term (-1) (Multiset.replicate 2 (pointVariable .plane ![1]))) := by
  decide +kernel

/-- The reconstruction step consumes the original relation, exact pivot and existing line seed. -/
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
  have h := WDVV.primary_point_eq A I F N H hsource hboundary Omega P T U S Hdiv hpair
    2 houtput ![2] SurfacePlaneGenusZero.conicLabels
    (by rw [conicPivot]; exact one_ne_zero) WDVVReplay.presentation WDVVReplay.accepted
  rw [RationalTerms.eval_eq_of_equivalent _ _ _ conicLower, conicPivot] at h
  rw [show SurfaceTarget.plane.effective.energy ![2] - 1 = 5 from by decide +kernel] at h
  have hseed : variableEval U P (pointVariable .plane ![1]) = 1 := by
    change (SurfaceQuery.points .plane 0 SurfaceTarget.plane.lineCurve 2).eval U = 1 at hline
    rw [show SurfaceTarget.plane.lineCurve = ![1] from by decide +kernel] at hline
    exact hline
  simpa only [RationalTerms.eval_term, Algebra.algebraMap_self_apply,
    Multiset.map_replicate, Multiset.prod_replicate, hseed, one_pow, mul_one,
    neg_neg, div_one] using h

end AxiomaticGWTest.Surfaces.GenusZeroStep
