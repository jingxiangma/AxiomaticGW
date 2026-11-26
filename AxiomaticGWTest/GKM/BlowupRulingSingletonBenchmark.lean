/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.Fixtures.BlowupRulingSingletonBenchmark
import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberOneMarking

/-! # Original ruling descendants, relative divisor signs, and the unit discrepancy -/

namespace AxiomaticGWTest.GKM.BlowupRulingSingletonBenchmark
open AxiomaticGW AxiomaticGW.GKM SurfaceGenusTwoBlowupDescendants BlowupTwoRuling

example (i : Fin 2) :
    (queryValue? 0 (request i .unit)).getD 0 -
      (queryValue? 0 (BlowupF1FiberOneMarking.requests 0)).getD 0 = -11/1920 := by
  rw [accepted, BlowupF1FiberOneMarking.accepted]
  change (-9 / 640 : ℚ) - (-1 / 120) = -11 / 1920
  norm_num

example : queryValue? 0 (⟨2, ![1, 0, 1], [⟨.exceptional 1, 3⟩]⟩ : SurfaceQuery X) =
    some (-23/2880) := by
  rw [← show request 0 (.exceptional 1) = ⟨2, ![1, 0, 1], [⟨.exceptional 1, 3⟩]⟩ by
    decide +kernel]
  exact accepted 0 (.exceptional 1)

example : queryValue? 0 (⟨2, ![0, 1, 1], [⟨.exceptional 1, 3⟩]⟩ : SurfaceQuery X) =
    some (1/2880) := by
  rw [← show request 1 (.exceptional 1) = ⟨2, ![0, 1, 1], [⟨.exceptional 1, 3⟩]⟩ by
    decide +kernel]
  exact accepted 1 (.exceptional 1)

example (i : Fin 2) (base : SurfaceAncestorKey X → ℚ) :
    SurfaceGenusTwo.ancestorValue base (SurfaceGenusTwo.oneMarkingKey (curve i) .unit 4) =
      1/576 := high_ancestors base i 0

example : BlowupRulingSingletonBenchmark.twoBlowups.card = 1057 :=
  BlowupRulingSingletonBenchmark.card_twoBlowups

end AxiomaticGWTest.GKM.BlowupRulingSingletonBenchmark
