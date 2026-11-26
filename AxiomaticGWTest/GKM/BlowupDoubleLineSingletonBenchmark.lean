/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.Fixtures.BlowupDoubleLineSingletonBenchmark

/-! # Signs and full curve labels for the five 2L descendants -/

namespace AxiomaticGWTest.GKM.BlowupDoubleLineSingletonBenchmark
open AxiomaticGW AxiomaticGW.GKM SurfaceGenusTwoBlowupDescendants BlowupTwoDoubleLine

example : queryValue? 0 (⟨2, ![0,0,2], [⟨.hyperplane, 3⟩]⟩ : SurfaceQuery .blowupTwo) =
    some (-3/320) := accepted .hyperplane

example (i : Fin 2) : queryValue? 0
    (⟨2, ![0,0,2], [⟨.exceptional i, 3⟩]⟩ : SurfaceQuery .blowupTwo) = some (-3/320) :=
  accepted (.exceptional i)

example : queryValue? 0 (⟨2, ![0,0,2], [⟨.unit, 4⟩]⟩ : SurfaceQuery .blowupTwo) =
    some (13/3840) := accepted .unit

example (base : SurfaceAncestorKey .blowupTwo → ℚ) :
    SurfaceGenusTwo.ancestorValue base (SurfaceGenusTwo.oneMarkingKey ![0,0,2] .point 2) = 0 :=
  point_ancestor base

example : BlowupDoubleLineSingletonBenchmark.twoBlowups.card = 1047 :=
  BlowupDoubleLineSingletonBenchmark.card_twoBlowups

end AxiomaticGWTest.GKM.BlowupDoubleLineSingletonBenchmark
