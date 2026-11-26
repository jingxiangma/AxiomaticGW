/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.Squares
public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.Affine

/-! # The 32 interior genus-two two-marked requests on the F₁ fiber

The indices, ordered requests and mixed calibration are taken from the
original reconstruction. All right-hand sides are obtained from its genus-two
relations and lower-genus recursion on the full effective class (0,1).
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

def values : Fin 32 → ℚ :=
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

/-- The original ordered stable-map descendant evaluator returns the stated rational. -/
theorem accepted (j : Fin 32) : queryValue? 0 (requests j) = some (values j) := by
  rw [query_affine, show lastAncestor = 0 from last_square]
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupF1FiberInteriorPairs
