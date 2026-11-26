/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.Fixtures.BlowupTwoRulingDivisorPoint

/-! # Full-class tests for the ruling divisor–point pairs -/

namespace AxiomaticGWTest.BlowupTwoRulingDivisorPoint
open AxiomaticGW SurfaceGenusTwoBlowupDescendants BlowupTwoRulingDivisorPoint

example : queryValue? 0 (⟨2, ![1, 0, 1], [⟨.exceptional 0, 2⟩, ⟨.point, 0⟩]⟩ :
    SurfaceQuery .blowupTwo) = some 0 := by
  rw [← show request 0 1 true false = ⟨2, ![1, 0, 1], [⟨.exceptional 0, 2⟩, ⟨.point, 0⟩]⟩ by
    decide +kernel]
  exact accepted 0 1 true false

example : queryValue? 0 (⟨2, ![0, 1, 1], [⟨.point, 1⟩, ⟨.exceptional 0, 1⟩]⟩ :
    SurfaceQuery .blowupTwo) = some (1/144) := by
  rw [← show request 1 2 false true = ⟨2, ![0, 1, 1], [⟨.point, 1⟩, ⟨.exceptional 0, 1⟩]⟩ by
    decide +kernel]
  exact accepted 1 2 false true

example (i : Fin 2) (order : Bool) : queryValue? 0 (request i 0 true order) = some (1/240) :=
  accepted i 0 true order

end AxiomaticGWTest.BlowupTwoRulingDivisorPoint
