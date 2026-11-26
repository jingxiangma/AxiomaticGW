/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleLinePairs
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineOneMarking
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoExceptionalOneMarking
public import AxiomaticGW.Surfaces.GenusTwoMarkedPairLookup

/-! # Original string, dilaton and divisor reconstruction of ordered pairs in 2L -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoDoubleLinePairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants EquivariantCoefficients

/-- The certified singleton table comes from the original mixed Bl₂ evaluator at 2L. -/
def singleton? : SurfaceQuery .blowupTwo → Option ℚ :=
  let labels := BlowupTwoExceptionalOneMarking.labels
  singletonTable? (fun j ↦ BlowupTwoDoubleLine.request (labels j))
    (fun j ↦ BlowupTwoDoubleLine.value (labels j))

private theorem singleton_sound (q : SurfaceQuery .blowupTwo) (v : ℚ)
    (h : singleton? q = some v) : queryValue? 0 q = some v :=
  singletonTable?_sound
    (fun j ↦ BlowupTwoDoubleLine.accepted (BlowupTwoExceptionalOneMarking.labels j)) q v h

/-- Native row indices for which one of the three original marked equations evaluates. -/
def markedRows : Finset (Fin 100) :=
  Finset.univ.filter fun j ↦ (markedPairValueWith? singleton? (requests j)).isSome

/-- Every successful marked reduction agrees with the independently held native value. -/
theorem marked_binding : ∀ j : Fin 100, (markedPairValueWith? singleton? (requests j)).all
    (· == values j) = true := by decide +kernel

/-- Precisely 50 of the 100 ordered pairs are recovered by the original marked equations. -/
theorem card_markedRows : markedRows.card = 50 := by decide +kernel

/-- The original reconstruction and both native coefficient checks for each recognized pair. -/
theorem marked_certified {j : Fin 100} (hj : j ∈ markedRows) :
    CheckedDescendant 0 (requests j) (values j) ∧ equivariant j = (values j : Coefficient) ∧
      Specializes (equivariant j) (values j) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hj).2
  have he := marked_binding j
  simp only [hv, Option.all_some, beq_iff_eq] at he
  exact ⟨markedPairValueWith?_checked 0 singleton_sound (he ▸ hv),
    BlowupTwoPositivePlaneEnergyTwoPairs.equivariant_eq_ordinary _,
    BlowupTwoPositivePlaneEnergyTwoPairs.specializes _⟩

end AxiomaticGW.GKM.BlowupTwoDoubleLinePairs
