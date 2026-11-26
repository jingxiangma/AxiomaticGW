/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.DivisorPointSquareValues
public import AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction
public import AxiomaticGW.Surfaces.GenusTwoFewMarkings

/-! # Twenty-four ordinary ruling descendants with a divisor and a point

At each ruling the divisor whose exceptional curve splits off the pencil gives
zero term by term. The hyperplane and the other exceptional divisor give 1/240
in the square and 1/144 in the product. Both marking orders use the original
mixed evaluator.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingDivisorPoint
open BlowupTwoRuling (X)
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- The nonzero product sources retain their original positions among all 25 graphs. -/
def productParts (j : Fin 3) : Fin 25 → ℚ := if j = 1 then 0 else
  ![-1/480, -161/12960, -161/12960, 5/162, 0, 0, 0, 0, 0, 0, 0, 13/4320,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 4000000 in
-- Every class assignment in each one of the 25 product graphs is retained.
/-- All six complete first-power products are checked before taking their sum. -/
theorem product_parts (i : Fin 2) (j : Fin 3) (n : Fin 25) :
    productSource i j n = productParts j n := by
  fin_cases i <;> fin_cases j <;> fin_cases n <;> decide +kernel

/-- The ordinary numbers depend on the divisor and on which of the two shapes is used. -/
def value (j : Fin 3) (square : Bool) : ℚ :=
  if j = 1 then 0 else if square then 1/240 else 1/144

/-- Full mixed descendant equality on both rulings and in both marking orders. -/
theorem accepted (i : Fin 2) (j : Fin 3) (square pointFirst : Bool) :
    queryValue? 0 (request i j square pointFirst) = some (value j square) := by
  rw [query_eq_leading]
  cases square
  · rw [product_sum]
    simp only [product_parts]
    fin_cases j <;> decide +kernel
  · rw [square_sum]
    simp only [square_parts]
    fin_cases j <;> decide +kernel

/-- Every marked pair lies in the original few-marking benchmark. -/
theorem domain (i : Fin 2) (j : Fin 3) (square pointFirst : Bool) :
    FewMarkingQuery (request i j square pointFirst) := by
  unfold FewMarkingQuery
  revert i j square pointFirst
  decide +kernel

/-- Arithmetic reconstruction witness for each of the 24 ordered requests. -/
theorem checked (i : Fin 2) (j : Fin 3) (square pointFirst : Bool) :
    CheckedDescendant 0 (request i j square pointFirst) (value j square) :=
  .mixed (accepted i j square pointFirst)

/-- Stable-map interpretation under the existing surface comparison and reconstruction inputs. -/
theorem accepted_from_geometry (i : Fin 2) (j : Fin 3) (square pointFirst : Bool) :
    type_of% (@SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
      (X := X) (i := 0) (q := request i j square pointFirst) (hg := rfl)
      (hv := checked i j square pointFirst)) :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
    (X := X) (i := 0) (q := request i j square pointFirst) (hg := rfl)
    (hv := checked i j square pointFirst)

end AxiomaticGW.BlowupTwoRulingDivisorPoint
