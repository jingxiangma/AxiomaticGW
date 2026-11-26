/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.LoopSquarePacketBinding

/-! # Shared-edge, disjoint-edge and omitted-refinement checks -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.LoopSquareRefinements

open AxiomaticGW AxiomaticGW.AdmcyclesHodgeStrataCandidates
open AxiomaticGW.GKM.LoopSquareRefinements

/-- The retained edge really is shared for every ordered loop pair. -/
theorem shared_edge : ∀ p ∈ pairs target, p.1.1 = p.2.1 := by
  decide +kernel

/-- Each retained edge is different in both two-edge refinement types. -/
theorem disjoint_edges :
    (∀ p ∈ pairs doubleLoop, p.1.1 ≠ p.2.1) ∧
    (∀ p ∈ pairs parallel, p.1.1 ≠ p.2.1) := by
  decide +kernel

/-- A loop plus a bridge contracts to the target only by retaining its loop;
therefore two such maps cannot generically cover its bridge. -/
theorem bridge_is_not_generic :
    pairs (rawIncidence7Candidate.toGraph rawIncidence7Valid) = ∅ := by
  decide +kernel

/-- An edgeless corolla has no candidate injection of the target edge. -/
theorem corolla_has_no_pairs :
    pairs (rawIncidence0Candidate.toGraph rawIncidence0Valid) = ∅ := by
  decide +kernel

/-- Both differently presented parallel occurrences retain their original slots. -/
theorem actual_parallel_slots :
    raw11Degree2Columns 18 = rawGraph28 ∧
    raw11Degree2Columns 21 = rawGraph31 ∧
    raw11Degree2Columns 23 = rawGraph12 := by
  exact ⟨rfl, rfl, rfl⟩

end AxiomaticGWTest.GKM.LoopSquareRefinements
