/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.DivisorPointTails
public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Third

/-! # Original product and pulled-square sources in the ruling divisor–point pairs -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingDivisorPoint
open BlowupTwoRuling (X curve)
open SurfaceGenusTwo SurfaceGenusTwoPositiveSquare SurfaceGenusTwoPositiveDivisorPairs

/-- The pulled-back cotangent square retains the point as its extra mark. -/
def squareLabels (i : Fin 2) (j : Fin 3) : Option (Fin 1) → SurfaceBasisLabel X :=
  fun k ↦ k.elim .point (fun _ ↦ divisor i j)

/-- The original product frame orders the divisor before the point. -/
def productLabels (i : Fin 2) (j : Fin 3) : Fin 2 → SurfaceBasisLabel X :=
  ![divisor i j, .point]

/-- One of the eleven signed pulled-square sources, including its extra-marking correction. -/
def squareSource (i : Fin 2) (j : Fin 3) (n : Fin 11) : ℚ :=
  pulledSquarePart ((BlowupTwoRuling.Third.backend i).vertex (ancestorValue low))
    1 (curve i) 0 (squareLabels i j) n

/-- One original signed product graph. The original low-cotangent genus-two base is retained. -/
def productSource (i : Fin 2) (j : Fin 3) (n : Fin 25) : ℚ :=
  productGraph ((BlowupTwoRuling.Third.backend i).vertex low) (curve i) (productLabels i j) n

/-- The original two-marking evaluator selects exactly the displayed outgoing square frame. -/
theorem square_sum (i : Fin 2) (j : Fin 3) : ancestorValue low (leading i j true) =
    ∑ n, squareSource i j n := by
  have h : ancestorValue low (leading i j true) =
      pulledSquare (vertex (ancestorValue low)) 1 (curve i) 0 (squareLabels i j) := by
    fin_cases i <;> fin_cases j
    all_goals
      rw [ancestorValue_pulledSquare low _ rfl (by decide +kernel) (by decide +kernel), ← vertex_eq]
      congr 1 <;> decide +kernel
  rw [h, pulledSquare_eq_parts, ← component_eq, ← (BlowupTwoRuling.Third.backend i).vertex_eq]
  rfl

/-- The original evaluator selects the two distinct first-power occurrences. -/
theorem product_sum (i : Fin 2) (j : Fin 3) : ancestorValue low (leading i j false) =
    ∑ n, productSource i j n := by
  have h : ancestorValue low (leading i j false) =
      ∑ n, productGraph (vertex low) (curve i) (productLabels i j) n := by
    rw [vertex_eq]
    fin_cases i <;> fin_cases j
    all_goals
      exact ancestorValue_twoMarking_product low _ rfl (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  rw [h, ← component_eq, ← (BlowupTwoRuling.Third.backend i).vertex_eq]
  rfl

end AxiomaticGW.BlowupTwoRulingDivisorPoint
