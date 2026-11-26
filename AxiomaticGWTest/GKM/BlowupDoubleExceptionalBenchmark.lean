module

import AxiomaticGW.GKM.Fixtures.BlowupDoubleExceptionalBenchmark

set_option linter.privateModule false

namespace AxiomaticGWTest.GKM.BlowupDoubleExceptionalBenchmark
open AxiomaticGW AxiomaticGW.GKM AxiomaticGW.SurfaceGenusTwoBlowupDescendants

-- The full E₂ degree, its own divisor and third power select the same ordinary scalar as E₁.
example : queryValue? 0 (⟨2, ![0, 2, 0], [⟨.exceptional 1, 3⟩]⟩ : SurfaceQuery .blowupTwo) =
    some (3/320) := by
  have eq : (⟨2, ![0, 2, 0], [⟨.exceptional 1, 3⟩]⟩ : SurfaceQuery .blowupTwo) =
      BlowupTwoDoubleExceptionalDivisor.request 1 := by decide +kernel
  rw [eq, BlowupTwoDoubleExceptionalDivisor.accepted]

-- The numerator and denominator are bound at the original E₁-class query.
example : queryValue? 0 (BlowupTwoDoubleExceptionalDivisor.request 0) ≠ some (29/5760) := by
  rw [BlowupTwoDoubleExceptionalDivisor.accepted]
  decide +kernel

-- Replacing the divisor by the other exceptional label changes the ordered request.
example : ∀ i : Fin 2, BlowupTwoDoubleExceptionalDivisor.request i ≠
    ⟨2, BlowupTwoDoubleExceptionalDivisor.beta i, [⟨.exceptional i.rev, 3⟩]⟩ := by decide +kernel

example : BlowupDoubleExceptionalBenchmark.twoBlowups.card = 908 :=
  BlowupDoubleExceptionalBenchmark.card_twoBlowups

end AxiomaticGWTest.GKM.BlowupDoubleExceptionalBenchmark
