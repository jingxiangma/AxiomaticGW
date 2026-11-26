/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineTransfer
public import AxiomaticGW.Surfaces.Fixtures.DoubleLineSingletons.Third
public import AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction
public import AxiomaticGW.Surfaces.GenusTwoFewMarkings

/-! # All five ordinary genus-two basis singletons on 2(H − E₁ − E₂)

The original one-marking square and calibration resolve these positive-plane-degree requests.
Every term at the full class uses a genus-zero or genus-one vertex. The proper-class terms
use the already certified primitive line and constant-curve ancestors.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLine
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoLineOneMarking (labels)
open BlowupTwoDoubleLineComponents.Third (backend)

/-- The ten unweighted original contractions at the unit or any of the three divisor states. -/
def graphValues (j : Fin 4) : Fin 10 → ℚ :=
  if j = 0 then ![0, 0, 0, -1/576, -1/12, -1/24, 0, -1/24, 0, -1]
  else ![-1/576, -1/576, 0, -1/288, -1/4, -1/6, 0, -1/12, -1/24, -3]

set_option maxRecDepth 65536
set_option Elab.async false

set_option maxHeartbeats 4000000 in
-- The ten distinct graphs retain all three splittings of the pure double strict line.
/-- Each of the forty individual non-point graph values comes from the original Bl₂ recursion. -/
theorem graph_values (j : Fin 4) (g : Fin 10) :
    graph backend (labels j) (2 - (labels j).codimension) g = graphValues j g := by
  fin_cases j <;> fin_cases g <;> decide +kernel

/-- The four leading ancestors are independent of the complete genus-two canonical base. -/
theorem high_ancestors (base : SurfaceAncestorKey .blowupTwo → ℚ) (j : Fin 4) :
    ancestorValue base (oneMarkingKey curve (labels j) (4 - (labels j).codimension)) =
      if j = 0 then -1/1152 else -29/5760 := by
  have h : 4 - (labels j).codimension = (2 - (labels j).codimension) + 2 := by
    fin_cases j <;> decide +kernel
  rw [h, ancestor_eq_sum backend]
  simp only [graph_values]
  fin_cases j <;> decide +kernel

/-- The complete ordinary values on the five surface basis states, with the strict-line signs. -/
def value : SurfaceBasisLabel .blowupTwo → ℚ
  | .unit => 13/3840
  | .point => 0
  | _ => -3/320

private theorem high_accepted (j : Fin 4) :
    queryValue? 0 (request (labels j)) = some (value (labels j)) := by
  rw [query_eq_leading, high_ancestors]
  fin_cases j <;> decide +kernel

/-- The original full-class mixed descendant evaluator on every basis singleton. -/
theorem accepted (a : SurfaceBasisLabel .blowupTwo) :
    queryValue? 0 (request a) = some (value a) := by
  cases a with
  | unit => exact high_accepted 0
  | hyperplane => exact high_accepted 1
  | point => exact point_accepted
  | exceptional i =>
    fin_cases i
    · exact high_accepted 2
    · exact high_accepted 3

/-- The original bounded benchmark includes the requests for all five basis labels. -/
theorem domain (a : SurfaceBasisLabel .blowupTwo) : FewMarkingQuery (request a) := by
  unfold FewMarkingQuery
  cases a with
  | exceptional i => fin_cases i <;> decide +kernel
  | _ => decide +kernel

/-- Checked arithmetic descendant witness in the full curve class. -/
theorem checked (a : SurfaceBasisLabel .blowupTwo) : CheckedDescendant 0 (request a) (value a) :=
  .mixed (accepted a)

/-- The stable-map descendant under the original geometric reconstruction hypotheses. -/
theorem accepted_from_geometry (a : SurfaceBasisLabel .blowupTwo) :
    type_of% (@SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
      (X := .blowupTwo) (i := 0) (q := request a) (hg := rfl) (hv := checked a)) :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
    (X := .blowupTwo) (i := 0) (q := request a) (hg := rfl) (hv := checked a)

end AxiomaticGW.BlowupTwoDoubleLine
