/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineBPConstants
public import AxiomaticGW.Surfaces.GenusTwoOneMarkingSquare

/-! # Genus-two one-marked ancestors in the strict-line class of the two-point blowup -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineOneMarking
open BlowupTwoLineBP SurfaceGenusTwo GenusTwoPsiSquare SurfacePointBenchmarkCache

private abbrev X := SurfaceTarget.blowupTwo

/-- The four basis insertions carrying at least two cotangent powers at L. -/
def labels : Fin 4 → SurfaceBasisLabel .blowupTwo :=
  ![.unit, .hyperplane, .exceptional 0, .exceptional 1]

private def graph (j : Fin 4) (i : Fin 10) : ℚ :=
  (boundaryTerm i).1.surfaceDecoratedEval X (constantVertexWithPoints X (genusZero X) (genusOne X))
    (boundaryTerm i).2 line (fun _ ↦ 1 - (labels j).codimension) (fun _ ↦ labels j)

private def graphValues (j : Fin 4) : Fin 10 → ℚ :=
  if j = 0 then ![1/576, 1/576, 0, 1/576, 1/6, 1/8, 0, 1/24, 1/24, 2] else
    ![1/288, 1/288, 1/576, 0, 1/12, 1/12, 0, 0, 1/24, 1]

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 1600000 in
-- The unit contributes one additional external power to the genus-zero and genus-one vertices.
private theorem unit_graph (i : Fin 10) : graph 0 i = graphValues 0 i := by
  fin_cases i <;> decide +kernel

private theorem hyperplane_graph (i : Fin 10) : graph 1 i = graphValues 1 i := by
  fin_cases i <;> decide +kernel

private theorem first_graph (i : Fin 10) : graph 2 i = graphValues 2 i := by
  fin_cases i <;> decide +kernel

private theorem second_graph (i : Fin 10) : graph 3 i = graphValues 3 i := by
  fin_cases i <;> decide +kernel

private theorem graph_eq (j : Fin 4) (i : Fin 10) : graph j i = graphValues j i := by
  fin_cases j
  · exact unit_graph i
  · exact hyperplane_graph i
  · exact first_graph i
  · exact second_graph i

/-- The square reduction gives 1/240 for the unit and 13/2880 for each of the
three divisors against the strict transform of the line through both points. -/
theorem high_ancestors (base : SurfaceAncestorKey .blowupTwo → ℚ) (j : Fin 4) :
    ancestorValue base (oneMarkingKey line (labels j) (3 - (labels j).codimension)) =
      if j = 0 then 1/240 else 13/2880 := by
  have hp : 3 - (labels j).codimension = (1 - (labels j).codimension) + 2 := by
    fin_cases j <;> decide +kernel
  rw [hp, ancestorValue_oneMarking_square, oneMarkingSquareValue,
    ← constantVertexWithPoints_eq X (genusZero X) (genusOne X) (genusZero_eq X) (genusOne_eq X)]
  change ∑ i, boundary (boundaryIndex i) * graph j i = _
  simp only [graph_eq]
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupTwoLineOneMarking
