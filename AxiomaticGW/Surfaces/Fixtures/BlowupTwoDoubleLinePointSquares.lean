/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLinePointPairs
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineIncidence

/-! # Genus-two cotangent squares with a point marking on the double strict line -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLinePointPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare
open BlowupTwoDoubleLine (curve)
open BlowupTwoDoubleLineIncidence (vertexZero vertexZero_sound)
open BlowupTwoDoubleLineComponents.Third (backend)

/-- Full-class two-marked square in the original order of the distinguished cotangent mark. -/
def squareIndex (i : Fin 5) : Fin 8 := i.castLE (by decide)

/-- Powers remaining after pulling the distinguished square off its marking. -/
def powers (i : Fin 5) : Option (Fin 1) → ℕ :=
  fun t ↦ Option.elim t (point (squareIndex i)).psi (fun _ ↦ (first (squareIndex i)).psi - 2)

/-- The point and the square's original labeled marking. -/
def labels (i : Fin 5) : Option (Fin 1) → SurfaceBasisLabel X :=
  fun t ↦ Option.elim t .point (fun _ ↦ (first (squareIndex i)).label)

/-- Signed pullback contribution, retaining each degree splitting and all node labelings. -/
def part (i : Fin 5) (g : Fin 11) : ℚ :=
  pulledSquarePart (backend.vertex (ancestorValue low)) 1 curve (powers i) (labels i) g

private theorem square_sum (i : Fin 5) :
    ancestorValue low (fullKey (squareIndex i)) = ∑ g, part i g := by
  have h : ancestorValue low (fullKey (squareIndex i)) =
      pulledSquare (vertex (ancestorValue low)) 1 curve (powers i) (labels i) := by
    fin_cases i
    all_goals
      rw [ancestorValue_pulledSquare low _ rfl (by decide +kernel) (by decide +kernel), ← vertex_eq]
      congr 1 <;> decide +kernel
  rw [h, pulledSquare_eq_parts, ← component_eq, ← backend.vertex_eq]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
-- Each of the eleven sources checks all degree splittings and both node labels.
/-- Each assignment in each signed square has a vanishing vertex by point incidence. -/
theorem point_support (i : Fin 5) (g : Fin 11) :
    pulledSquareZero (vertexZero (ancestorValue low)) 1 curve (powers i) (labels i) g = true := by
  fin_cases i <;> fin_cases g <;> decide +kernel

/-- Every individual graph contraction vanishes in these original 2L squares. -/
theorem part_zero (i : Fin 5) (g : Fin 11) : part i g = 0 :=
  pulledSquarePart_eq_zero_of_support _ _ (vertexZero_sound backend (ancestorValue low))
    _ _ _ _ g (point_support i g)

/-- Both original ordered descendants vanish for each of the five point-containing squares. -/
theorem square_accepted (i : Fin 5) (last : Bool) :
    SurfaceGenusTwoBlowupDescendants.queryValue? 0 (request (squareIndex i) last) = some 0 := by
  rw [query_from_ancestor, square_sum]
  simp only [part_zero, Finset.sum_const_zero]

end AxiomaticGW.BlowupTwoDoubleLinePointPairs
