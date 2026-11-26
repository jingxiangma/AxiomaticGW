/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsOnePoint
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine

/-!
# Nonzero plane genus-two descendants from the accepted canonical table

The arithmetic sector alone uses candidate canonical data. These regressions
compose its three computations with the already accepted line table, certifying
the original descendant algorithm at each full incoming GKM request.
-/

@[expose] public section

namespace AxiomaticGWTest.GKM.PlaneGenusTwoOnePoint

open AxiomaticGW BelorousskiPandharipande
open AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay

/-- All three one-marked requests use the accepted table, without extra seeds. -/
theorem accepted (i : Fin 3) :
    planeQueryValue? (requests ⟨i.val, by omega⟩) = some (values ⟨i.val, by omega⟩) := by
  have hb : (requests ⟨i.val, by omega⟩).beta 0 ≤ 1 := by
    fin_cases i <;> decide +kernel
  rw [← planeQueryValueWith?_eq 1 GenusTwoPlaneLine.values GenusTwoPlaneLine.accepted _ hb]
  change planeQueryValueWith? canonicalValues _ = _
  simpa only [Nat.zero_add] using OnePoint.computed i

example : planeQueryValue? ⟨2, ![1], [⟨.unit, 5⟩]⟩ = some (1 / 128) :=
  accepted 0

example : planeQueryValue? ⟨2, ![1], [⟨.hyperplane, 4⟩]⟩ = some (-1 / 960) :=
  accepted 1

example : planeQueryValue? ⟨2, ![1], [⟨.point, 3⟩]⟩ = some (-1 / 240) :=
  accepted 2

end AxiomaticGWTest.GKM.PlaneGenusTwoOnePoint
