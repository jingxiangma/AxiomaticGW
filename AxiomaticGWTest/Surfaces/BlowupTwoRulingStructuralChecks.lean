/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.Fixtures.RulingPairs.BPValues
import AxiomaticGW.Surfaces.Fixtures.RulingPairs.PointTerminal
import AxiomaticGW.Surfaces.Fixtures.RulingPairs.ShiftedSources

/-! # Tests of the full classes, ordered point slots and unshifted ruling equations -/

namespace AxiomaticGWTest.BlowupTwoRulingStructuralChecks
open AxiomaticGW SurfaceGenusTwoBlowupDescendants
open BlowupTwoRulingInterior

example (i : Fin 2) : (atRuling i).card = 50 := card_atRuling i

example : queryValue? 0
    (⟨2, ![0,1,1], [⟨.point, 0⟩, ⟨.point, 1⟩]⟩ : SurfaceQuery .blowupTwo) =
      some (SurfaceGenusTwoBlowupRecursion.values (X := .blowupTwo) 0 (![0,1,1], .point)) := by
  have hq : request 1 .point .point false =
      ⟨2, ![0,1,1], [⟨.point, 0⟩, ⟨.point, 1⟩]⟩ := by decide +kernel
  have hc : BlowupTwoRuling.curve 1 = ![0,1,1] := by decide +kernel
  simpa only [hq, hc] using point_point 1 false

example : BlowupTwoRuling.BP.actual (BlowupTwoRuling.curve 1, .exceptional 1) = 0 :=
  (BlowupTwoRuling.BP.dependencies 1).2.1

example : BlowupTwoRuling.BP.actual (BlowupTwoRuling.curve 1, .exceptional 0) =
    BlowupTwoRuling.BP.actual (BlowupTwoRuling.curve 1, .point) :=
  (BlowupTwoRuling.BP.dependencies 1).2.2

example : BlowupTwoRuling.H.shifted 0 = ![2,0,1] ∧ BlowupTwoRuling.H.shifted 1 = ![1,1,1] := by
  decide +kernel

end AxiomaticGWTest.BlowupTwoRulingStructuralChecks
