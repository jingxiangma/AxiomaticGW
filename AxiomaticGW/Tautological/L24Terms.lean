/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Gluing
public import AxiomaticGW.Tautological.Fixtures.L24Claims
public import AxiomaticGW.Tautological.DecoratedGluingMarkingBounds

/-!
# Executable terms for the complete L24 equation

The held coefficient data and checked gluing constructions are usable without
initializing the original relation-search contexts. Interpretation and support
are checked here; geometric vanishing is proved separately in `L24GW`.
-/

@[expose] public section

namespace AxiomaticGW.L24Relation
open RelationCertificate GluingExpression PsiBoundaryExpansion

-- Membership elimination reduces the same 815-column data as the graph replay.
set_option maxRecDepth 20000

/-- Exactly the nonzero held coefficients, with their checked gluing constructions. -/
def cotangentRelation : CotangentCombination 2 (Fin 4) :=
  (Finset.univ.filter fun i : Fin 815 ↦ L24CorrectionsReplay.fullClaim i ≠ 0).val.map
    (fun i ↦ (L24CorrectionsReplay.fullClaim i, L24Gluing.term i))

/-- Removing zero coefficients changes neither the full class nor its normalization. -/
theorem cotangentRelation_strata : cotangentRelation.strata =
    interpret L24Graphs.columns L24CorrectionsReplay.fullClaim := by
  simp only [cotangentRelation, CotangentCombination.strata, Multiset.map_map,
    Function.comp_def, ← Finset.sum_eq_multiset_sum, L24Gluing.term_stratum,
    interpret_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : L24CorrectionsReplay.fullClaim i = 0
  · simp only [h, ne_eq, not_true_eq_false, if_false, zero_smul]
  · rw [if_pos h]

/-- The complete equation retains every one of its 721 nonzero columns. -/
theorem cotangentRelation_card : cotangentRelation.card = 721 := by
  decide +kernel

/-- Every original decorated term has exactly the L24 codimension. -/
theorem cotangentRelation_codimension : ∀ t ∈ cotangentRelation,
    (t.2.expression.decoratedGraph t.2.decoration).codimension = 3 := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ht
  change ((L24Gluing.term i).expression.decoratedStratum
    (L24Gluing.term i).decoration).codimension = 3
  rw [L24Gluing.term_stratum]
  exact (L24Graphs.graph_degree i).1

/-- Every signed added-marking term retains the original codimension. -/
theorem added_term_codimension (n : ℕ)
    (t : ℚ × CotangentTerm 2 (ExtraMarkings n (Fin 4)))
    (ht : t ∈ cotangentRelation.pullback n) :
    (t.2.expression.decoratedGraph t.2.decoration).codimension = 3 := by
  obtain ⟨z, hz, w, hw, rfl⟩ :=
    (CotangentCombination.mem_pullback cotangentRelation n t).mp ht
  exact ((z.2.addMarkings_bounds n w hw).1).trans (cotangentRelation_codimension z hz)

end AxiomaticGW.L24Relation
