/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.SquareHead
public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.Products
public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.Low

/-! # Fiber-frame reconstruction before the final degree-five square

Only the two marking orders of the second and third unit descendants depend
on this square. The other 30 original mixed descendants are fully numerical.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

def fixed : Fin 32 → ℚ :=
  Fin.addCases (m := 19) (n := 13) (Fin.lastCases 0 headValues)
    (Fin.addCases (m := 4) (n := 9) productValues (fun _ ↦ 0))

def coefficient : Fin 32 → ℚ :=
  Fin.addCases (m := 19) (n := 13) (Fin.lastCases 1 (fun _ ↦ 0)) (fun _ ↦ 0)

/-- The only uncontracted variable in these 32 mixed rows is an actual original ancestor. -/
abbrev lastAncestor := SurfaceGenusTwo.ancestorValue low (squareKey 18)

theorem ancestors_affine (j : Fin 32) :
    ancestorValueWith boundary (key j) = fixed j + coefficient j * lastAncestor := by
  change SurfaceGenusTwo.ancestorValue low (key j) = _
  refine Fin.addCases (m := 19) (n := 13) (fun i ↦ ?_) (fun i ↦ ?_) j
  · simp only [key, fixed, coefficient, Fin.addCases_left]
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · change lastAncestor = 0 + 1 * lastAncestor
      rw [one_mul, zero_add]
    · simp only [Fin.lastCases_castSucc, zero_mul, add_zero]
      exact first_squares k
  · simp only [key, fixed, coefficient, Fin.addCases_right, zero_mul, add_zero]
    refine Fin.addCases (m := 4) (n := 9) (fun k ↦ ?_) (fun k ↦ ?_) i
    · simpa only [Fin.addCases_left] using product_values k
    · simpa only [Fin.addCases_right] using low_values k

private theorem linear_sum (terms : List (ℚ × Fin 32)) (x : ℚ) :
    (terms.map (fun t ↦ t.1 * (fixed t.2 + coefficient t.2 * x))).sum =
    (terms.map (fun t ↦ t.1 * fixed t.2)).sum +
      (terms.map (fun t ↦ t.1 * coefficient t.2)).sum * x := by
  induction terms with
  | nil => simp only [List.map_nil, List.sum_nil, zero_mul, zero_add]
  | cons t rest ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

def offsets : Fin 32 → ℚ :=
  ![(-3 / 80),
    (-3 / 80),
    (-19 / 480),
    (-107 / 2880),
    (-59 / 1440),
    (-113 / 2880),
    (1 / 72),
    (7 / 1440),
    (-107 / 2880),
    (-19 / 480),
    (1 / 160),
    (1 / 160),
    (-11 / 1440),
    (-1 / 160),
    (1 / 144),
    (1 / 240),
    (-113 / 2880),
    (-59 / 1440),
    (-1 / 160),
    (-11 / 1440),
    (-29 / 1440),
    (-29 / 1440),
    (1 / 144),
    (1 / 240),
    (7 / 1440),
    (1 / 72),
    (1 / 240),
    (1 / 144),
    (1 / 240),
    (1 / 144),
    0,
    0]

def unitCoefficient (j : Fin 32) : ℚ := if j.val < 2 then 1 else 0

/-- The two unit rows depend with coefficient one on the final square. -/
theorem query_affine (j : Fin 32) :
    queryValue? 0 (requests j) = some (offsets j + unitCoefficient j * lastAncestor) := by
  rw [query_from_ancestors]
  simp only [ancestors_affine, linear_sum]
  rw [show ((row j).map (fun t ↦ t.1 * fixed t.2)).sum = offsets j by
      fin_cases j <;> decide +kernel,
    show ((row j).map (fun t ↦ t.1 * coefficient t.2)).sum = unitCoefficient j by
      fin_cases j <;> decide +kernel]

/-- The last 30 local rows already evaluate without the degree-five square. -/
theorem thirty_accepted (j : Fin 30) :
    queryValue? 0 (requests (Fin.natAdd 2 j)) = some (offsets (Fin.natAdd 2 j)) := by
  rw [query_affine, show unitCoefficient (Fin.natAdd 2 j) = 0 by fin_cases j <;> decide +kernel,
    zero_mul, add_zero]

end AxiomaticGW.BlowupF1FiberInteriorPairs
