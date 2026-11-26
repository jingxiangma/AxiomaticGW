/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHRequest
public import AxiomaticGW.Surfaces.Fixtures.CertifiedComponentLayers
public import AxiomaticGW.Surfaces.GenusTwoOneMarkingSquare

/-! # Genus-two one-marked ancestors in the double exceptional class on F₁

The leading terms at the full class 2E use the ten cotangent-square boundary graphs.
Class splittings may contain two copies of E. The lower-genus vertices use
the same certified point evaluators on all such summands.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1DoubleExceptionalOneMarking
open SurfaceGenusTwo GenusTwoPsiSquare SurfaceGenusTwoPositiveSquare BlowupF1FiberHReduction

/-- The full doubled exceptional curve in the ordered (E,F) coordinates. -/
abbrev doubleExceptional : target.Curve := ![2, 0]

/-- The four basis labels in the order used by the incoming localization frame. -/
def labels : Fin 4 → SurfaceBasisLabel target := ![.unit, .hyperplane, .exceptional 0, .point]

/-- The four leading ancestor contributions before stable-map cotangent transfer. -/
def mainValues : Fin 4 → ℚ := ![-1/1152, 0, 29/5760, 0]

private theorem bounded_vertex_eq :
    (CertifiedComponents.bounded target).vertex (fun _ ↦ 0) = constantVertex target := by
  rw [CertifiedComponents.vertex_eq, component_eq, SurfaceGenusTwoPositiveDivisorPairs.vertex_eq]
  funext g S inst h beta k a
  exact eval_zero_vertexTerms target g S h beta k a

private def graph (j : Fin 4) (i : Fin 10) : ℚ :=
  (boundaryTerm i).1.surfaceDecoratedEval target
    ((CertifiedComponents.bounded target).vertex (fun _ ↦ 0))
    (boundaryTerm i).2 doubleExceptional (fun _ ↦ 2 - (labels j).codimension) (fun _ ↦ labels j)

private def graphValues (j : Fin 4) : Fin 10 → ℚ :=
  if j = 0 then ![0, 0, 0, -1/576, -1/12, -1/24, 0, -1/24, 0, -1]
  else if j = 2 then ![1/576, 1/576, 0, 1/288, 1/4, 1/6, 0, 1/12, 1/24, 3]
  else 0

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
    ancestorValue base (oneMarkingKey doubleExceptional (labels j) (4 - (labels j).codimension)) =
      mainValues j := by
  have hp : 4 - (labels j).codimension = 2 - (labels j).codimension + 2 := by
    fin_cases j <;> decide +kernel
  rw [hp, ancestorValue_oneMarking_square, oneMarkingSquareValue,
    ← bounded_vertex_eq]
  change ∑ i, GenusTwoPsiSquare.boundary (boundaryIndex i) * graph j i = _
  simp only [graph_eq]
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupF1DoubleExceptionalOneMarking
