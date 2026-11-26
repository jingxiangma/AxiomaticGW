/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNEEEKSupport

/-! Consumers of the actual exceptional BP coefficient at proper plane-zero remainders. -/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupNEEEKSupport
open AxiomaticGW SurfaceGenusTwoBlowupNEEEKSupport

/-- The degree-two Bl2P2 full class has its selected exceptional coefficient minus twelve. -/
theorem degree_two_same_class :
    RationalTerms.coefficient
      (SurfaceGenusTwoBlowupNRelation.bpRow .blowupTwo
        (SurfaceTarget.blowupTwo.effective.energy ![0, 0, 2])
        (![0, 0, 2] + SurfaceTarget.blowupTwo.exceptionalCurve 0)
        ![.exceptional 0, .exceptional 0, .exceptional 0])
      {Sum.inr (SurfaceFirstDescendant.query 2 ![0, 0, 2] (.exceptional 0)
        (SurfaceTarget.blowupTwo.effective.energy ![0, 0, 2]))} = -12 := by
  rw [normalized_eee_k_proper_remainder .blowupTwo 0 0 ![0, 0, 2] ![0, 0, 2]
    (SurfaceTarget.blowupTwo.exceptionalCurve 0) rfl rfl (by decide +kernel)]
  rfl

/-- A foreign exceptional remainder cannot contribute to the selected K column. -/
theorem foreign_exceptional_remainder :
    RationalTerms.coefficient
      (SurfaceGenusTwoBlowupNRelation.bpRow .blowupTwo
        (SurfaceTarget.blowupTwo.effective.energy ![0, 1, 2])
        (![0, 1, 2] + SurfaceTarget.blowupTwo.exceptionalCurve 0)
        ![.exceptional 0, .exceptional 0, .exceptional 0])
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0, 2] (.exceptional 0)
        (SurfaceTarget.blowupTwo.effective.energy ![1, 0, 2]))} = 0 := by
  rw [normalized_eee_k_proper_remainder .blowupTwo 0 0 ![0, 1, 2] ![1, 0, 2]
    (SurfaceTarget.blowupTwo.exceptionalCurve 1) (by decide +kernel) rfl (by decide +kernel)]
  decide +kernel

/-- A reducible plane-zero remainder of higher energy is excluded with both
coordinates retained. -/
theorem mixed_high_energy_remainder :
    RationalTerms.coefficient
      (SurfaceGenusTwoBlowupNRelation.bpRow .blowupTwo
        (SurfaceTarget.blowupTwo.effective.energy ![1, 3, 2])
        (![1, 3, 2] + SurfaceTarget.blowupTwo.exceptionalCurve 0)
        ![.exceptional 0, .exceptional 0, .exceptional 0])
      {Sum.inr (SurfaceFirstDescendant.query 2 ![0, 0, 2] (.exceptional 0)
        (SurfaceTarget.blowupTwo.effective.energy ![0, 0, 2]))} = 0 := by
  rw [normalized_eee_k_proper_remainder .blowupTwo 0 0 ![1, 3, 2] ![0, 0, 2]
    ![2, 3, 0] (by decide +kernel) rfl (by decide +kernel)]
  decide +kernel

/-- The requested class-zero exceptional descendant remains included without energy positivity. -/
theorem class_zero_kept :
    RationalTerms.coefficient
      (SurfaceGenusTwoBlowupNRelation.bpRow .hirzebruchOne 0
        (SurfaceTarget.hirzebruchOne.exceptionalCurve 0)
        ![.exceptional 0, .exceptional 0, .exceptional 0])
      {Sum.inr (SurfaceFirstDescendant.query 2 0 (.exceptional 0) 0)} = -12 := by
  have h := normalized_eee_k_proper_remainder .hirzebruchOne 0 0 0 0
    (SurfaceTarget.hirzebruchOne.exceptionalCurve 0) rfl rfl (by decide +kernel)
  simpa only [zero_add, map_zero, and_self, ite_true] using h

end AxiomaticGWTest.SurfaceGenusTwoBlowupNEEEKSupport

