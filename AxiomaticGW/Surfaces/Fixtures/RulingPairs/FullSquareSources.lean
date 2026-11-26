/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.Transfer
public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.SingletonVertices
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPositiveDivisorPairs
public import AxiomaticGW.Surfaces.GenusTwoPulledSquare

/-! # The full-class pulled-square sources in all ruling interiors

The square is chosen by the ordinary marked ancestor evaluator. The ruling
and its subclasses use their genuine singleton ancestors whenever a genus-two
component meets a one-marked stable flag.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingInterior.FullSquares
open BlowupTwoRuling (X)
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants SurfaceGenusTwoPositiveSquare
open SurfaceGenusTwoPositiveDivisorPairs
open BlowupTwoDoubleLine (terminals)

/-- There are twenty squares with a raised unit or divisor, and one more with a raised point. -/
def shape (r : Fin 21) : Fin 5 × Fin 5 :=
  if hr : r.val < 20 then (⟨r.val / 5, by omega⟩, ⟨r.val % 5, by omega⟩) else (4, 0)

/-- The full-class marked ancestor represented by a given square. -/
def key (i : Fin 2) (r : Fin 21) := leading i (shape r).1 (shape r).2

/-- At least one original marking carries two cotangent powers. -/
theorem has_square (i : Fin 2) (r : Fin 21) : (squareMarks (key i r)).Nonempty := by
  fin_cases i <;> fin_cases r <;> decide +kernel

/-- Signed contribution of the original graph after selecting the actual marked square. -/
def part (i : Fin 2) (r : Fin 21) (g : Fin 11) : ℚ :=
  let q := key i r
  let h := has_square i r
  pulledSquarePart ((BlowupTwoRuling.Third.backend i).vertex
    (BlowupTwoRuling.SingletonVertices.next i)) (q.orderedInsertions.length - 1) q.beta
    (squareLowerPowers q h) (q.orderedLabels ∘ squareFrame q h) g

/-- All full-class pulled squares are the sum of their eleven genuine signed boundary sources. -/
theorem sum_parts (i : Fin 2) (r : Fin 21) :
    ancestorValueWith terminals (key i r) = ∑ g, part i r g := by
  let low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals
  change ancestorValue low _ = _
  rw [ancestorValue_pulledSquare low _ rfl (by fin_cases i <;> fin_cases r <;> decide +kernel)
    (has_square i r), ← vertex_eq, pulledSquare_eq_parts, ← component_eq,
    ← (BlowupTwoRuling.Third.backend i).vertex_eq]
  simp only [part, BlowupTwoRuling.SingletonVertices.next_eq]
  rfl

end AxiomaticGW.BlowupTwoRulingInterior.FullSquares
