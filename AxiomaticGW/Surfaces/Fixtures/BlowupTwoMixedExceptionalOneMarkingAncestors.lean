/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoExceptionalOneMarking
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalSingletons.ThirdPower

/-! # Genus-two singleton squares in the class E₁ + E₂ on the two-point blowup

The ten signed graphs use the original cotangent-square relation. Their full
effective-class splitting includes both orderings of E₁ and E₂. Every contracted
graph evaluates to zero for each of the five basis insertions.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalOneMarking
open SurfaceGenusTwo GenusTwoPsiSquare SurfaceGenusTwoPositiveSquare

/-- The class E₁ + E₂ in the ordered basis E₁, E₂, L. -/
abbrev beta : SurfaceTarget.blowupTwo.Curve := ![1, 1, 0]

/-- The fixed manifest order is unit, hyperplane, E₁, E₂, and point. -/
abbrev labels := BlowupTwoExceptionalOneMarking.labels

private abbrev components := BlowupTwoMixedExceptionalSingletonComponents.ThirdPower.components

private def squareGraph (j : Fin 5) (i : Fin 10) : ℚ :=
  (boundaryTerm i).1.surfaceDecoratedEval .blowupTwo
    (components.vertex (fun _ ↦ 0))
    (boundaryTerm i).2 beta (fun _ ↦ 2 - (labels j).codimension) (fun _ ↦ labels j)

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 4000000 in
-- Each of the ten graphs includes every full-class assignment and every inverse-metric contraction.
private theorem squareGraph_unit (i : Fin 10) : squareGraph 0 i = 0 := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the ten original graphs for each of the four non-unit basis states.
private theorem squareGraph_nonunit (j : Fin 4) (i : Fin 10) : squareGraph j.succ i = 0 := by
  fin_cases j <;> fin_cases i <;> decide +kernel

/-- Each leading ancestor is determined before the genus-two canonical lookup. -/
theorem main_ancestors (base : SurfaceAncestorKey .blowupTwo → ℚ) (j : Fin 5) :
    ancestorValue base (oneMarkingKey beta (labels j) (4 - (labels j).codimension)) = 0 := by
  have hv : components.vertex (fun _ ↦ 0) =
      constantVertex .blowupTwo := by
    rw [CertifiedComponents.vertex_eq, component_eq, SurfaceGenusTwoPositiveDivisorPairs.vertex_eq]
    funext g S inst h b d a
    exact eval_zero_vertexTerms .blowupTwo g S h b d a
  have hp : 4 - (labels j).codimension = 2 - (labels j).codimension + 2 := by
    fin_cases j <;> decide +kernel
  have hz (i : Fin 10) : squareGraph j i = 0 := by
    exact Fin.cases (squareGraph_unit i) (fun k ↦ squareGraph_nonunit k i) j
  rw [hp, ancestorValue_oneMarking_square, oneMarkingSquareValue, ← hv]
  change ∑ i, GenusTwoPsiSquare.boundary (boundaryIndex i) * squareGraph j i = 0
  simp only [hz, mul_zero, Finset.sum_const_zero]

end AxiomaticGW.BlowupTwoMixedExceptionalOneMarking
