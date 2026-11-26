module

import AxiomaticGW.GKM.Fixtures.BlowupDoubleExceptionalPairBenchmark

set_option linter.privateModule false

namespace AxiomaticGWTest.GKM.BlowupDoubleExceptionalPairBenchmark
open AxiomaticGW AxiomaticGW.GKM AxiomaticGW.SurfaceGenusTwoBlowupDescendants
open BlowupTwoDoubleExceptionalPairs

-- The reversed divisor equation retains the own divisor and the negative curve intersection.
example : CheckedDescendant 0
    (⟨2, ![0, 2, 0], [⟨.exceptional 1, 3⟩, ⟨.exceptional 1, 0⟩]⟩ : SurfaceQuery .blowupTwo)
    (-3/160) := by
  have hq : (⟨2, ![0, 2, 0], [⟨.exceptional 1, 3⟩, ⟨.exceptional 1, 0⟩]⟩ :
    SurfaceQuery .blowupTwo) = request 1 2 true := by decide +kernel
  rw [hq]
  exact checked 1 2 true

-- The marked divisor branch retains the lowered point insertion and its negative sign.
example : ∀ i : Fin 2, let d : SurfaceBasisLabel .blowupTwo := .exceptional i
    let s : SurfaceInsertion .blowupTwo := ⟨d, 3⟩
    d.primaryFactor (BlowupTwoDoubleExceptionalDivisor.beta i) = -2 ∧
      SurfaceGenusTwo.cupCoefficient d s = -1 ∧
      SurfaceGenusTwo.cupInsertion d s = ⟨.point, 2⟩ := by decide +kernel

example : request 0 0 false ≠ request 0 1 false ∧ request 0 0 false ≠ request 0 0 true := by
  decide +kernel

example : BlowupDoubleExceptionalPairBenchmark.twoBlowups.card = 920 :=
  BlowupDoubleExceptionalPairBenchmark.card_twoBlowups

end AxiomaticGWTest.GKM.BlowupDoubleExceptionalPairBenchmark
