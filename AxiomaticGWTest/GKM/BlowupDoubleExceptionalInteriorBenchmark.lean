/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.Fixtures.BlowupDoubleExceptionalInteriorBenchmark

/-! # Ordinary genus-two regression on both doubled exceptional axes -/

namespace AxiomaticGWTest.GKM.BlowupDoubleExceptionalInteriorBenchmark
open AxiomaticGW AxiomaticGW.GKM
open SurfaceGenusTwoBlowupDescendants BlowupTwoDoubleExceptionalInteriorPairs
open BlowupTwoDoubleExceptionalDivisor (beta)

example (i : Fin 2) : queryValue? 0 (⟨2, beta i, [⟨.unit, 2⟩, ⟨.unit, 3⟩]⟩ : SurfaceQuery X) =
    some (27/1280) := accepted i 0

example : queryValue? 0 (⟨2, ![0,2,0], [⟨.exceptional 1, 1⟩, ⟨.unit, 3⟩]⟩ : SurfaceQuery X) =
    some (37/1920) := by
  have hr : requests 1 24 = ⟨2, ![0,2,0], [⟨.exceptional 1, 1⟩, ⟨.unit, 3⟩]⟩ := by decide +kernel
  rw [← hr, ← show values 1 24 = 37/1920 by decide +kernel]
  exact accepted 1 24

example : queryValue? 0 (⟨2, ![2,0,0], [⟨.exceptional 1, 1⟩, ⟨.unit, 3⟩]⟩ : SurfaceQuery X) =
    some 0 := by
  have hr : requests 0 24 = ⟨2, ![2,0,0], [⟨.exceptional 1, 1⟩, ⟨.unit, 3⟩]⟩ := by decide +kernel
  rw [← hr, ← show values 0 24 = 0 by decide +kernel]
  exact accepted 0 24

example : queryValue? 0
    (⟨2, ![2,0,0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 1⟩]⟩ : SurfaceQuery X) =
    some (-7/160) := by
  have hr : requests 0 21 = ⟨2, ![2,0,0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 1⟩]⟩ := by
    decide +kernel
  rw [← hr, ← show values 0 21 = -7/160 by decide +kernel]
  exact accepted 0 21

example (i : Fin 2) : (BlowupDoubleExceptionalInteriorBenchmark.axisSuite i).card = 105 :=
  (BlowupDoubleExceptionalInteriorBenchmark.axis_coverage i).1

example : BlowupDoubleExceptionalInteriorBenchmark.twoBlowups.card = 1042 :=
  BlowupDoubleExceptionalInteriorBenchmark.card_twoBlowups

end AxiomaticGWTest.GKM.BlowupDoubleExceptionalInteriorBenchmark
