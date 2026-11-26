/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineInteriorTransfer
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineIncidence
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoExceptionalOneMarking
public import AxiomaticGW.Surfaces.GenusTwoPulledSquare

/-! # The sixteen full-class two-marked squares on twice the strict line

The original ancestor itself selects its squared cotangent occurrence and all exterior powers.
Every curve splitting and constituent vertex stays on the strict line.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLineInterior
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare
open BlowupTwoDoubleLine (curve)

/-- The two-marked ancestor in the first sixteen positions of the actual mixed transfer. -/
abbrev fullKey (j : Fin 16) := key (j.castAdd 40)

/-- Genus-two singleton already determined on L or 2L, identified by its complete marked key. -/
def singletonKey (c : Fin 2) (j : Fin 5) : SurfaceAncestorKey X :=
  let a := BlowupTwoExceptionalOneMarking.labels j
  oneMarkingKey (if c = 0 then ![0, 0, 1] else curve) a (3 + c.val - a.codimension)

/-- Proved leading ancestor values, including the signed difference between L and 2L. -/
def singletonValue (c : Fin 2) (j : Fin 5) : ℚ :=
  if j = 4 then 0 else if c = 0 then (if j = 0 then 1/240 else 13/2880)
  else (if j = 0 then -1/1152 else -29/5760)

private theorem singleton_value (c : Fin 2) (j : Fin 5) :
    ancestorValue low (singletonKey c j) = singletonValue c j := by
  fin_cases c <;> fin_cases j
  · exact BlowupTwoLineOneMarking.high_ancestors low 0
  · exact BlowupTwoLineOneMarking.high_ancestors low 1
  · exact BlowupTwoLineOneMarking.high_ancestors low 2
  · exact BlowupTwoLineOneMarking.high_ancestors low 3
  · rw [ancestorValue_low _ _ rfl (by decide +kernel)]
    decide +kernel
  · exact BlowupTwoDoubleLine.high_ancestors low 0
  · exact BlowupTwoDoubleLine.high_ancestors low 1
  · exact BlowupTwoDoubleLine.high_ancestors low 2
  · exact BlowupTwoDoubleLine.high_ancestors low 3
  · exact BlowupTwoDoubleLine.point_ancestor low

/-- Use an already-proved singleton at a genus-two vertex when its full curve and powers match. -/
def next (q : SurfaceAncestorKey X) : ℚ :=
  let r := ((List.finRange 2).product (List.finRange 5)).find?
    (fun p ↦ decide (singletonKey p.1 p.2 = q))
  r.elim (ancestorValue low q) (fun p ↦ singletonValue p.1 p.2)

theorem next_eq (q : SurfaceAncestorKey X) : next q = ancestorValue low q := by
  unfold next
  cases h : List.find? _ _ with
  | none => rfl
  | some r =>
    have hq : singletonKey r.1 r.2 = q :=
      of_decide_eq_true (List.find?_some (p := fun p : Fin 2 × Fin 5 ↦
        decide (singletonKey p.1 p.2 = q)) h)
    exact hq ▸ (singleton_value r.1 r.2).symm

/-- Every full-class key contains a squared cotangent occurrence. -/
theorem has_square (j : Fin 16) : (squareMarks (fullKey j)).Nonempty := by
  fin_cases j <;> decide +kernel

/-- An individual signed contraction with the actual marking selected by the ancestor recursion. -/
def contractedPart (v : SurfaceVertexValues X ℚ) (j : Fin 16) (g : Fin 11) : ℚ :=
  let q := fullKey j
  pulledSquarePart v (q.orderedInsertions.length - 1) q.beta (squareLowerPowers q (by
    exact has_square j)) (q.orderedLabels ∘ squareFrame q (by exact has_square j)) g

/-- Each term uses its own effective splittings, node contractions and full strict-line class. -/
def squarePart (c : CertifiedComponents X) (j : Fin 16) (g : Fin 11) : ℚ :=
  contractedPart (c.vertex next) j g

/-- The eleven original sources, including the smooth-square rational-tail correction. -/
theorem square_sum (c : CertifiedComponents X) (j : Fin 16) :
    ancestorValue low (fullKey j) = ∑ g, squarePart c j g := by
  rw [ancestorValue_pulledSquare low _ (by fin_cases j <;> rfl) (by fin_cases j <;> decide +kernel)
    (has_square j), ← vertex_eq, pulledSquare_eq_parts, ← component_eq, ← c.vertex_eq]
  simp only [squarePart, contractedPart, funext next_eq]

end AxiomaticGW.BlowupTwoDoubleLineInterior
