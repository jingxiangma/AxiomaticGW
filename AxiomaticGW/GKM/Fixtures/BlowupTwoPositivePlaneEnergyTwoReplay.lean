/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoEnergyTwoSingletonComparison
public import AxiomaticGW.GKM.Fixtures.BlowupTwoPositivePlaneEnergyTwoPairs
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineOneMarking
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoRulingOneMarking
public import AxiomaticGW.Surfaces.GenusTwoMarkedPairLookup

/-! # Target-side reconstruction on the three positive-plane curves of energy two

Each singleton comes from the original mixed evaluator. The resulting finite table
evaluates both orders of the string, dilaton and divisor pair reductions.
-/

@[expose] public section
namespace AxiomaticGW.GKM
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants EquivariantCoefficients

namespace BlowupTwoPositivePlaneEnergyTwoSingletons

private theorem original_rows : ∀ j : Fin 15,
    (∃ a, (requests j, values j) = (BlowupTwoDoubleLine.request a, BlowupTwoDoubleLine.value a)) ∨
    ∃ i a, (requests j, values j) = (BlowupTwoRuling.request i a, BlowupTwoRuling.value i a) := by
  decide +kernel

/-- Ordinary mixed reconstruction in exactly the incoming full class and ordered marking. -/
theorem evaluated (j : Fin 15) : queryValue? 0 (requests j) = some (values j) := by
  rcases original_rows j with ⟨a, h⟩ | ⟨i, a, h⟩
  · exact (congrArg (fun p ↦ queryValue? 0 p.1 = some p.2) h).mpr (BlowupTwoDoubleLine.accepted a)
  · exact (congrArg (fun p ↦ queryValue? 0 p.1 = some p.2) h).mpr (BlowupTwoRuling.accepted i a)

/-- Original arithmetic witness for all fifteen basis singletons. -/
theorem accepted (j : Fin 15) : CheckedDescendant 0 (requests j) (values j) := .mixed (evaluated j)

/-- Original Bl₂ reconstruction, equality of full fractions and ordinary specialization. -/
theorem certified (j : Fin 15) : CheckedDescendant 0 (requests j) (values j) ∧
    equivariant j = (values j : Coefficient) ∧ Specializes (equivariant j) (values j) :=
  ⟨accepted j, equivariant_eq_ordinary j, specializes j⟩

/-- Both rulings' original unit descendants differ from the reconstructed F₁ fiber by −11/1920. -/
theorem ruling_unit_discrepancy (i : Fin 2) :
    CheckedDescendant 0 (requests (rulingIndex i 0)) (values (rulingIndex i 0)) ∧
    equivariant (rulingIndex i 0) = F1FiberOneMarking.equivariant 0 - 11/1920 := by
  refine ⟨accepted _, ?_⟩
  rw [(ruling i 0).2]
  norm_num
  ring

end BlowupTwoPositivePlaneEnergyTwoSingletons

namespace BlowupTwoPositivePlaneEnergyTwoPairs

/-- The original fifteen mixed reconstructions, keyed by their full singleton requests. -/
def singleton? := singletonTable? BlowupTwoPositivePlaneEnergyTwoSingletons.requests
  BlowupTwoPositivePlaneEnergyTwoSingletons.values

/-- Ordered rows admitting the original string, dilaton or divisor computation. -/
def markedRows : Finset (Fin 300) :=
  Finset.univ.filter fun j ↦ (markedPairValueWith? singleton? (requests j)).isSome

/-- Exactly fifty of the hundred pairs on each class reduce by one of these three equations. -/
theorem marked_counts : markedRows.card = 150 ∧ ∀ c : Fin 3,
    (markedRows.filter (fun j ↦
      (requests j).beta = BlowupTwoPositivePlaneEnergyTwoSingletons.curves c)).card = 50 := by
  decide +kernel

private theorem agrees : ∀ j : Fin 300, (markedPairValueWith? singleton? (requests j)).all
    (· == values j) = true := by decide +kernel

/-- Each recognized pair agrees with its original two-point-blowup evaluation. -/
theorem marked_accepted {j : Fin 300} (h : j ∈ markedRows) :
    CheckedDescendant 0 (requests j) (values j) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp h).2
  have he := agrees j
  simp only [hv, Option.all_some, beq_iff_eq] at he
  exact markedPairValueWith?_checked 0
    (singletonTable?_sound BlowupTwoPositivePlaneEnergyTwoSingletons.evaluated) (he ▸ hv)

/-- Claim-bound original evaluation, complete equivariant field and regular specialization. -/
theorem marked_certified {j : Fin 300} (h : j ∈ markedRows) :
    CheckedDescendant 0 (requests j) (values j) ∧ equivariant j = (values j : Coefficient) ∧
    Specializes (equivariant j) (values j) :=
  ⟨marked_accepted h, equivariant_eq_ordinary j, specializes j⟩

end BlowupTwoPositivePlaneEnergyTwoPairs
end AxiomaticGW.GKM
