/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.F1FiberPairs
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberMarkedPairs

/-! # The 32 string, dilaton and primary-divisor pairs in the genus-two fiber report

The eight blocks place the primary unit, first descendant unit, H or E in either
slot. Each block runs through the four dimension-compatible surviving insertions.
The index and value comparisons retain the complete ordered incoming requests.
-/

@[expose] public section
namespace AxiomaticGW.GKM.F1FiberPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants BlowupF1FiberMarkedPairs

/-- Indices in the 64-row incoming frame, grouped by equation, slot and surviving basis label. -/
def markedIndices (i : Fin 32) : Fin 64 :=
  (#[0, 6, 11, 16, 5, 24, 40, 55, 1, 7, 12, 17, 4, 23, 39, 54,
    20, 25, 29, 33, 10, 28, 44, 58, 36, 41, 45, 49, 15, 32, 48, 61] :
    Array (Fin 64))[i.val]'i.isLt

private def markedRow (i : Fin 32) :
    {p : SurfaceQuery .hirzebruchOne × ℚ // CheckedDescendant 0 p.1 p.2} :=
  let k := Fin.ofNat 4 i.val
  let last := i.val / 4 % 2 == 1
  if i.val < 16 then
    let rule : UnitEquation := if i.val < 8 then .string else .dilaton
    ⟨(unitRequest rule last k, rule.factor * BlowupF1FiberOneMarking.values k),
      .unitPair (unit_accepted rule last k)⟩
  else
    let d : Fin 2 := if i.val < 24 then 0 else 1
    ⟨(divisorRequest d last k, divisorValues d k), .divisorPair (divisor_accepted d last k)⟩

private theorem marked_binding : ∀ i : Fin 32,
    (markedRow i).val = (requests (markedIndices i), values (markedIndices i)) := by decide +kernel

/-- The checked descendant evidence applies to each actual incoming query and ordinary value. -/
theorem marked_accepted (i : Fin 32) :
    CheckedDescendant 0 (requests (markedIndices i)) (values (markedIndices i)) := by
  have h := (markedRow i).property
  rwa [marked_binding i] at h

/-- The subframe contains exactly the ordered fiber pairs recognized by the marked equations. -/
theorem marked_coverage : ∀ j : Fin 64, (∃ i : Fin 32, markedIndices i = j) ↔
    (unitPairReduction? (requests j)).isSome ∨ (divisorPairReduction? (requests j)).isSome := by
  decide +kernel

/-- Apply a successful marked-equation test directly at the incoming request index. -/
theorem marked_accepted_of_recognized (j : Fin 64)
    (h : (unitPairReduction? (requests j)).isSome ∨ (divisorPairReduction? (requests j)).isSome) :
    CheckedDescendant 0 (requests j) (values j) := by
  obtain ⟨i, rfl⟩ := (marked_coverage j).2 h
  exact marked_accepted i

end AxiomaticGW.GKM.F1FiberPairs
