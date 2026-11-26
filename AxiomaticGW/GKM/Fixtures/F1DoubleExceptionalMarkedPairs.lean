/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalOneMarkingReplay
public import AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalPairs
public import AxiomaticGW.Surfaces.GenusTwoMarkedPairLookup

/-! # Exceptional support and marked equations for two insertions in class 2E on F₁ -/

@[expose] public section
namespace AxiomaticGW.GKM.F1DoubleExceptionalPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- Exact lookup in the certified four-singleton frame. -/
def singleton? (q : SurfaceQuery .hirzebruchOne) : Option ℚ :=
  singletonTable? F1DoubleExceptionalOneMarking.requests F1DoubleExceptionalOneMarking.values q

/-- Prefer the point-support vanishing, then apply a marked equation to the singleton frame. -/
def reducedValue? (q : SurfaceQuery .hirzebruchOne) : Option ℚ :=
  supportedMarkedPairValueWith? singleton? q

/-- Indices resolved by exceptional point support, string, dilaton or a primary divisor. -/
def reducedIndices : Finset (Fin 64) :=
  Finset.univ.filter fun i ↦ (reducedValue? (requests i)).isSome

/-- These methods cover 46 ordered pairs in class 2E. -/
theorem card_reducedIndices : reducedIndices.card = 46 := by decide +kernel

private theorem binding : ∀ i, i ∈ reducedIndices →
    reducedValue? (requests i) = some (values i) := by decide +kernel

/-- Each accepted native value follows from point support or the proved singleton reconstruction. -/
theorem reduced_accepted {i : Fin 64} (hi : i ∈ reducedIndices) :
    CheckedDescendant 0 (requests i) (values i) :=
  supportedMarkedPairValueWith?_checked 0
    (singletonTable?_sound F1DoubleExceptionalOneMarking.accepted) (binding i hi)

end AxiomaticGW.GKM.F1DoubleExceptionalPairs
