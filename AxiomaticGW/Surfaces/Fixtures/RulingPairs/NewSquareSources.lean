/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.ProperFrame
public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Third
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.IncidenceSquares
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineTransfer

/-! # Proper-class pulled squares specific to the two ruling calibrations

Five constant-class and ten primitive exceptional marked profiles supplement
the original proper keys from the doubled-axis and doubled-line equations.
Each source retains the additional marking and the full node pairing.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingInterior.NewSquares
open BlowupTwoRuling (X)
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants SurfaceGenusTwoPositiveSquare
open SurfaceGenusTwoPositiveDivisorPairs
open BlowupTwoDoubleLine (terminals)

/-- The original low-cotangent terminal function with the checked energy-one table. -/
abbrev low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals

/-- The new profiles, with constant-class profiles first. -/
def index : Fin 15 → Fin 30 := ![0, 1, 2, 3, 7, 8, 9, 10, 11, 16, 17, 18, 19, 21, 23]

/-- The complete key in the original mixed calibration. -/
def slot (j : Fin 15) : Fin 68 := squareIndex (index j)

/-- Powers remaining after subtracting the square at the selected second marking. -/
def powers (i : Fin 2) (j : Fin 15) : Option (Fin 1) → ℕ :=
  fun t ↦ t.elim (tailFirst i (slot j)).psi (fun _ ↦ (tailSecond i (slot j)).psi - 2)

/-- The additional insertion and the insertion carrying the selected square. -/
def labels (i : Fin 2) (j : Fin 15) : Option (Fin 1) → SurfaceBasisLabel X :=
  fun t ↦ t.elim (tailFirst i (slot j)).label (fun _ ↦ (tailSecond i (slot j)).label)

/-- One original signed graph, including the extra-marking correction at index zero. -/
def part (i : Fin 2) (j : Fin 15) (g : Fin 11) : ℚ :=
  pulledSquarePart ((BlowupTwoRuling.Third.backend i).vertex (ancestorValue low))
    1 (tailCurve i (slot j)) (powers i j) (labels i j) g

/-- Original square elimination in the selected marking frame. -/
theorem sum_parts (i : Fin 2) (j : Fin 15) :
    ancestorValueWith terminals (properKey i (slot j)) = ∑ g, part i j g := by
  change ancestorValue low _ = _
  have h : ancestorValue low (properKey i (slot j)) = pulledSquare
      (vertex (ancestorValue low)) 1 (tailCurve i (slot j)) (powers i j) (labels i j) := by
    fin_cases i <;> fin_cases j
    all_goals
      rw [ancestorValue_pulledSquare low _ rfl (by decide +kernel) (by decide +kernel), ← vertex_eq]
      congr 1 <;> decide +kernel
  rw [h, pulledSquare_eq_parts, ← component_eq, ← (BlowupTwoRuling.Third.backend i).vertex_eq]
  rfl

end AxiomaticGW.BlowupTwoRulingInterior.NewSquares
