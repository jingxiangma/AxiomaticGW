/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Third
public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Transfer
public import AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction
public import AxiomaticGW.Surfaces.GenusTwoFewMarkings

/-! # All ten ordinary genus-two basis singletons in the two rulings of Bl₂

Each pencil has a reducible member with positive summands `Eᵢ` and `L`. The
original graph sums and the proper-class calibration terms retain these full
curve classes. In particular the leading unit ancestor is nonzero.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open SurfaceGenusTwoPositiveSquare GenusTwoPsiSquare

/-- Original contraction with all degree splittings, signed by the original graph flags. -/
def graph (i : Fin 2) (j : Fin 5) (n : Fin 10) : ℚ :=
  (boundaryTerm n).1.surfaceDecoratedEval X ((Third.backend i).vertex (fun _ ↦ 0))
    (boundaryTerm n).2 (curve i) (fun _ ↦ 2 - (label i j).codimension) (fun _ ↦ label i j)

/-- The ten individual graph contractions in the relative order of the marking labels. -/
def graphValues (j : Fin 5) : Fin 10 → ℚ :=
  if j = 0 then ![0, 0, 0, 1/288, 1/6, 1/12, 0, 1/12, 0, 2]
  else if j = 2 then 0
  else if j = 4 then ![1/144, 1/144, 1/144, 0, 0, 0, 0, 0, 0, 0]
  else ![-1/64, -1/64, 0, -1/72, -3/4, -5/12, 0, -1/3, -3/8, -1]

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 8000000 in
-- All ten original source graphs retain every splitting at each target and basis state.
/-- The original lower-genus evaluations of all one hundred marked graph sources. -/
theorem graph_values (i : Fin 2) (j : Fin 5) (n : Fin 10) :
    graph i j n = graphValues j n := by
  fin_cases i <;> fin_cases j <;> fin_cases n <;> decide +kernel

/-- Leading ancestors before the proper-class transfer terms. -/
def leadingValues : Fin 5 → ℚ := ![1/576, -23/1152, 0, -23/1152, 7/1440]

/-- The cotangent-square relation determines every leading ancestor for any genus-two base. -/
theorem high_ancestors (base : SurfaceAncestorKey X → ℚ) (i : Fin 2) (j : Fin 5) :
    ancestorValue base (oneMarkingKey (curve i) (label i j) (4 - (label i j).codimension)) =
      leadingValues j := by
  have hp : 4 - (label i j).codimension = (2 - (label i j).codimension) + 2 := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hv : (Third.backend i).vertex (fun _ ↦ 0) = constantVertex X := by
    rw [CertifiedComponents.vertex_eq, component_eq, SurfaceGenusTwoPositiveDivisorPairs.vertex_eq]
    funext g S inst h b d a
    exact eval_zero_vertexTerms X g S h b d a
  rw [hp, ancestorValue_oneMarking_square, oneMarkingSquareValue, ← hv]
  change ∑ n, GenusTwoPsiSquare.boundary (boundaryIndex n) * graph i j n = leadingValues j
  simp only [graph_values]
  fin_cases j <;> decide +kernel

/-- Ordinary descendant values, distinguishing both exceptional divisor insertions. -/
def value (i : Fin 2) : SurfaceBasisLabel X → ℚ
  | .unit => -9/640
  | .hyperplane => -7/960
  | .exceptional k => if i = k then 1/2880 else -23/2880
  | .point => 1/240

private theorem indexed_accepted (i : Fin 2) (j : Fin 5) :
    queryValue? 0 (request i (label i j)) = some (value i (label i j)) := by
  rw [query_eq_leading, high_ancestors]
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- The full mixed evaluator reconstructs all ten basis singletons at their original queries. -/
theorem accepted (i : Fin 2) (a : SurfaceBasisLabel X) :
    queryValue? 0 (request i a) = some (value i a) := by
  cases a with
  | unit => exact indexed_accepted i 0
  | hyperplane => exact indexed_accepted i 1
  | point => exact indexed_accepted i 4
  | exceptional k =>
    fin_cases i <;> fin_cases k
    · exact indexed_accepted 0 2
    · exact indexed_accepted 0 3
    · exact indexed_accepted 1 3
    · exact indexed_accepted 1 2

/-- The bounded benchmark contains all ten requests. -/
theorem domain (i : Fin 2) (a : SurfaceBasisLabel X) : FewMarkingQuery (request i a) := by
  unfold FewMarkingQuery
  fin_cases i <;> cases a with
  | exceptional k => fin_cases k <;> decide +kernel
  | _ => decide +kernel

/-- Checked arithmetic witness in the full ruling class. -/
theorem checked (i : Fin 2) (a : SurfaceBasisLabel X) :
    CheckedDescendant 0 (request i a) (value i a) := .mixed (accepted i a)

/-- Stable-map interpretation under the project's geometric reconstruction hypotheses. -/
theorem accepted_from_geometry (i : Fin 2) (a : SurfaceBasisLabel X) :
    type_of% (@SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
      (X := X) (i := 0) (q := request i a) (hg := rfl) (hv := checked i a)) :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
    (X := X) (i := 0) (q := request i a) (hg := rfl) (hv := checked i a)

end AxiomaticGW.BlowupTwoRuling
