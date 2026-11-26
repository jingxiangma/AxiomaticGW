/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module
public import AxiomaticGW.Surfaces.GenusTwoBlowupNMixedKSupport
@[expose] public section
namespace AxiomaticGWTest.SurfaceGenusTwoBlowupNMixedKSupport
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupNRelation
open SurfaceGenusTwoBlowupNMixedKSupport

/-- The proper E_i split retains its H factor despite negative signed multiplicity. -/
theorem negative_multiplicity_eeh_k :
    RationalTerms.coefficient (bpRow SurfaceTarget.blowupTwo
      (SurfaceTarget.blowupTwo.effective.energy ![2, 0, 1])
      (![2, 0, 1] + SurfaceTarget.blowupTwo.exceptionalCurve 0)
      ![.exceptional 0, .exceptional 0, .hyperplane])
      {Sum.inr (SurfaceFirstDescendant.query 2 ![2, 0, 1] (.exceptional 0)
        (SurfaceTarget.blowupTwo.effective.energy ![2, 0, 1]))} = -6 := by
  have h := normalized_eeh_k_proper_remainder SurfaceTarget.blowupTwo 0 0
    ![2, 0, 1] ![2, 0, 1] (SurfaceTarget.blowupTwo.exceptionalCurve 0) rfl
    (SurfaceTarget.blowupTwo.planeDegree_exceptionalCurve 0) (by decide +kernel)
  exact h.trans (by decide +kernel)

/-- The other exceptional label remains a distinct zero column at the same full class. -/
theorem different_exceptional_label_zero :
    RationalTerms.coefficient (bpRow SurfaceTarget.blowupTwo
      (SurfaceTarget.blowupTwo.effective.energy ![1, 1, 1])
      (![1, 1, 1] + SurfaceTarget.blowupTwo.exceptionalCurve 0)
      ![.exceptional 0, .exceptional 0, .hyperplane])
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 1, 1] (.exceptional 1)
        (SurfaceTarget.blowupTwo.effective.energy ![1, 1, 1]))} = 0 := by
  have h := normalized_eeh_k_proper_remainder SurfaceTarget.blowupTwo 0 1
    ![1, 1, 1] ![1, 1, 1] (SurfaceTarget.blowupTwo.exceptionalCurve 0) rfl
    (SurfaceTarget.blowupTwo.planeDegree_exceptionalCurve 0) (by decide +kernel)
  exact h.trans (by decide +kernel)

/-- A full reducible remainder of energy two is retained and has zero K coefficient. -/
theorem reducible_exceptional_remainder_zero :
    RationalTerms.coefficient (bpRow SurfaceTarget.blowupTwo
      (SurfaceTarget.blowupTwo.effective.energy ![2, 0, 1])
      (![2, 0, 1] + SurfaceTarget.blowupTwo.exceptionalCurve 0)
      ![.exceptional 0, .exceptional 0, .hyperplane])
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0, 1] (.exceptional 0)
        (SurfaceTarget.blowupTwo.effective.energy ![1, 0, 1]))} = 0 := by
  have h := normalized_eeh_k_proper_remainder SurfaceTarget.blowupTwo 0 0
    ![2, 0, 1] ![1, 0, 1] ![2, 0, 0] (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  exact h.trans (by decide +kernel)

/-- The degree-two F1 coefficient keeps the linear factor -6d. -/
theorem hirzebruch_degree_two_eeh_k :
    RationalTerms.coefficient (bpRow SurfaceTarget.hirzebruchOne
      (SurfaceTarget.hirzebruchOne.effective.energy ![0, 2])
      (![0, 2] + SurfaceTarget.hirzebruchOne.exceptionalCurve 0)
      ![.exceptional 0, .exceptional 0, .hyperplane])
      {Sum.inr (SurfaceFirstDescendant.query 2 ![0, 2] (.exceptional 0)
        (SurfaceTarget.hirzebruchOne.effective.energy ![0, 2]))} = -12 := by
  have h := normalized_eeh_k_proper_remainder SurfaceTarget.hirzebruchOne 0 0
    ![0, 2] ![0, 2] (SurfaceTarget.hirzebruchOne.exceptionalCurve 0) rfl
    (SurfaceTarget.hirzebruchOne.planeDegree_exceptionalCurve 0) (by decide +kernel)
  exact h.trans (by decide +kernel)

/-- The degree-zero pure exceptional sector has the actual zero EEH coefficient. -/
theorem pure_exceptional_eeh_k_zero :
    RationalTerms.coefficient (bpRow SurfaceTarget.hirzebruchOne
      (SurfaceTarget.hirzebruchOne.effective.energy ![1, 0])
      (![1, 0] + SurfaceTarget.hirzebruchOne.exceptionalCurve 0)
      ![.exceptional 0, .exceptional 0, .hyperplane])
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0] (.exceptional 0)
        (SurfaceTarget.hirzebruchOne.effective.energy ![1, 0]))} = 0 := by
  have h := normalized_eeh_k_proper_remainder SurfaceTarget.hirzebruchOne 0 0
    ![1, 0] ![1, 0] (SurfaceTarget.hirzebruchOne.exceptionalCurve 0) rfl
    (SurfaceTarget.hirzebruchOne.planeDegree_exceptionalCurve 0) (by decide +kernel)
  exact h.trans (by decide +kernel)

/-- EHH keeps no nonprimary column at any proper exceptional remainder. -/
theorem ehh_proper_exceptional_zero :
    RationalTerms.coefficient (bpRow SurfaceTarget.blowupTwo
      (SurfaceTarget.blowupTwo.effective.energy ![1, 0, 1])
      (![1, 0, 1] + SurfaceTarget.blowupTwo.exceptionalCurve 0)
      ![.exceptional 0, .hyperplane, .hyperplane])
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0, 1] (.exceptional 0)
        (SurfaceTarget.blowupTwo.effective.energy ![1, 0, 1]))} = 0 := by
  apply normalized_ehh_nonprimary_proper_remainder SurfaceTarget.blowupTwo 0
    ![1, 0, 1] _ _ (SurfaceTarget.blowupTwo.exceptionalCurve 0) rfl
    (SurfaceTarget.blowupTwo.planeDegree_exceptionalCurve 0) (by decide +kernel)
  exact fun gamma n ↦ SurfaceFirstDescendant.query_ne_points _ gamma _ _ n

end AxiomaticGWTest.SurfaceGenusTwoBlowupNMixedKSupport
