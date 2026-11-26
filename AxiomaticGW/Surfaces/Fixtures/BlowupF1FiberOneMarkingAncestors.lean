/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHRequest
public import AxiomaticGW.Surfaces.GenusTwoL24PointCache
public import AxiomaticGW.Surfaces.GenusTwoOneMarkingSquare
public import AxiomaticGW.Surfaces.PointBenchmarkCache

/-! # Genus-two one-marked ancestors in the fiber class on F₁

Each row contracts the ten original cotangent-square boundary graphs against
the certified genus-zero and genus-one point evaluators.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberOneMarking
open SurfaceGenusTwo GenusTwoPsiSquare SurfacePointBenchmarkCache BlowupF1FiberHReduction

/-- The four basis labels in the order used by the incoming localization frame. -/
def labels : Fin 4 → SurfaceBasisLabel target := ![.unit, .hyperplane, .exceptional 0, .point]

/-- The four leading ancestor contributions before stable-map cotangent transfer. -/
def mainValues : Fin 4 → ℚ := ![0, -1/60, -1/60, 7/1440]

private def graph (j : Fin 4) (i : Fin 10) : ℚ :=
  (boundaryTerm i).1.surfaceDecoratedEval target
    (constantVertexWithPoints target (genusZero target) (genusOne target))
    (boundaryTerm i).2 fiber (fun _ ↦ 2 - (labels j).codimension) (fun _ ↦ labels j)

private def graphValues (j : Fin 4) : Fin 10 → ℚ :=
  if j = 0 then 0 else if j = 3 then ![1/144, 1/144, 1/144, 0, 0, 0, 0, 0, 0, 0] else
    ![-1/72, -1/72, 0, -1/72, -2/3, -1/3, 0, -1/3, -1/3, 0]

set_option Elab.async false
set_option maxRecDepth 65536

private theorem point_graph (i : Fin 10) : graph 3 i = graphValues 3 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 1600000 in
-- The unit carries two external cotangent powers before the graph contractions.
private theorem unit_graph (i : Fin 10) : graph 0 i = graphValues 0 i := by
  fin_cases i <;> decide +kernel

private theorem hyperplane_graph (i : Fin 10) : graph 1 i = graphValues 1 i := by
  fin_cases i <;> decide +kernel

private theorem exceptional_graph (i : Fin 10) : graph 2 i = graphValues 2 i := by
  fin_cases i <;> decide +kernel

private theorem graph_eq (j : Fin 4) (i : Fin 10) : graph j i = graphValues j i := by
  fin_cases j
  · exact unit_graph i
  · exact hyperplane_graph i
  · exact exceptional_graph i
  · exact point_graph i

/-- The original square determines all four leading terms independently of the genus-two base. -/
theorem main_ancestors (base : SurfaceAncestorKey target → ℚ) (j : Fin 4) :
    ancestorValue base (oneMarkingKey fiber (labels j) (4 - (labels j).codimension)) =
      mainValues j := by
  have hp : 4 - (labels j).codimension = 2 - (labels j).codimension + 2 := by
    fin_cases j <;> decide +kernel
  rw [hp, ancestorValue_oneMarking_square, oneMarkingSquareValue,
    ← constantVertexWithPoints_eq target (genusZero target) (genusOne target)
      (genusZero_eq target) (genusOne_eq target)]
  change ∑ i, GenusTwoPsiSquare.boundary (boundaryIndex i) * graph j i = _
  simp only [graph_eq]
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupF1FiberOneMarking
