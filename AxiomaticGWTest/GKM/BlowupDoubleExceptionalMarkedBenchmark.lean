module

import AxiomaticGW.GKM.Fixtures.BlowupDoubleExceptionalMarkedBenchmark

set_option linter.privateModule false

namespace AxiomaticGWTest.GKM.BlowupDoubleExceptionalMarkedBenchmark
open AxiomaticGW AxiomaticGW.GKM
open BlowupTwoDoubleExceptionalMarked

-- At 2E₂ the primary E₂ acting on a unit descendant uses both nonzero singleton terms:
-- −2 (13/3840) + 3/320 = 1/384. A primary E₁ has zero curve intersection and zero cup value here.
example : values 1 4 .unit = 1/384 ∧ values 1 3 .unit = 0 := by decide +kernel

-- Both orders of the nonzero two-term correction are independently checked.
example (last : Bool) :
    SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 (request 1 4 .unit last) (1/384) := by
  have h : values 1 4 .unit = 1/384 := by decide +kernel
  rw [← h]
  exact checked 1 4 .unit last

-- The class-and-dimension matched pair with two positive exceptional cotangent powers
-- has no supported string, dilaton or primary-divisor reduction.
example : (⟨2, ![2, 0, 0], [⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 2⟩]⟩ :
    SurfaceQuery .blowupTwo) ∉ atAxis 0 := by
  rw [mem_atAxis_iff]
  decide +kernel

example : BlowupDoubleExceptionalMarkedBenchmark.twoBlowups.card = 978 :=
  BlowupDoubleExceptionalMarkedBenchmark.card_twoBlowups

end AxiomaticGWTest.GKM.BlowupDoubleExceptionalMarkedBenchmark
