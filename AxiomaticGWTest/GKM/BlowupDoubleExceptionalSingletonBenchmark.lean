module

import AxiomaticGW.GKM.Fixtures.BlowupDoubleExceptionalSingletonBenchmark

set_option linter.privateModule false

namespace AxiomaticGWTest.GKM.BlowupDoubleExceptionalSingletonBenchmark
open AxiomaticGW AxiomaticGW.GKM SurfaceGenusTwoBlowupDescendants
open BlowupTwoDoubleExceptionalSingletons

-- Exchanging the two exceptional labels changes the own/foreign result at fixed full class.
example : queryValue? 0 (request 0 (.exceptional 0)) ≠
    queryValue? 0 (request 0 (.exceptional 1)) := by
  rw [accepted, accepted]
  decide +kernel

-- The fourth cotangent power belongs to the unit on both axes.
example (i : Fin 2) : queryValue? 0 (request i .unit) = some (13/3840) ∧
    (request i .unit).insertions = [⟨.unit, 4⟩] := ⟨accepted i _, rfl⟩

-- The two old points and two old divisor singletons account for the entire overlap.
example : (BlowupDoubleExceptionalPairBenchmark.twoBlowups ∩
    BlowupDoubleExceptionalSingletonBenchmark.singletons).card = 4 :=
  BlowupDoubleExceptionalSingletonBenchmark.overlap

end AxiomaticGWTest.GKM.BlowupDoubleExceptionalSingletonBenchmark
