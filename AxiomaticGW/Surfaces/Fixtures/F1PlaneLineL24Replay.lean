/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineTable
public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineIncidenceVertices

/-! # Complete numerical genus-two grid through energy three on the one-point blowup

Two point conditions at 2E+F violate the incidence constraint. This proves termwise
vanishing of the lower-genus L24 graphs and the two class-zero coefficient sums.
The unchanged original row checker then certifies all twenty-four states.
-/

@[expose] public section
namespace AxiomaticGW.F1PlaneLineIncidence
open SurfaceGenusTwo

private theorem impossible :
    ¬Allowed F1PlaneLine.shifted (2 • tag .point + profile F1PlaneLine.labels) := by decide +kernel

/-- Every individual original weighted lower-genus contraction at 2E+F vanishes. -/
theorem shifted_lower_zero (j : Fin 815) : F1PlaneLine.weighted j = 0 := by
  unfold F1PlaneLine.weighted
  dsimp only
  split_ifs
  · rfl
  · apply mul_eq_zero_of_right
    unfold guardedConstantPointContractionWithPoints
    split_ifs
    · rfl
    · rw [GluingExpression.scalarPointContraction_eq]
      exact point_graph_zero _ 2 (fun m _ ↦ pull_zero _ original_vertex_zero m) _ _ _
        _ _ (le_refl _) impossible

/-- Both class-zero divisor columns vanish, including all twenty-seven genus-two diagrams. -/
theorem shifted_divisor_zero (b : Label) : F1PlaneLine.divisorCoefficient b = 0 := by
  unfold F1PlaneLine.divisorCoefficient
  apply Finset.sum_eq_zero
  intro j _
  apply mul_eq_zero_of_right
  change remainderPointCoefficient X (requested b) (firstCoefficientVertex X 0 b 0)
    (L24Gluing.term j) F1PlaneLine.shifted 2 F1PlaneLine.labels = 0
  rw [remainderPointCoefficient_eq X (requested b) (firstCoefficientVertex X 0 b 0)
    (firstCoefficientVertex_eq (X := X) 0 b 0)]
  change pointCoefficient X (requested b) _ (0 + F1PlaneLine.shifted) 2 _ = 0
  rw [zero_add]
  unfold pointCoefficient
  split_ifs
  · exact point_graph_zero _ 2 (fun m _ ↦ pull_zero _ (coefficient_vertex_zero b) m) _ _ _
      _ _ (le_refl _) impossible
  · rfl

end AxiomaticGW.F1PlaneLineIncidence

namespace AxiomaticGW.F1PlaneLine
open F1PlaneLineIncidence SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupBoundedCertificate

/-- The absolute hyperplane first descendant obtained from the original shifted L24 row. -/
theorem hyperplane_value : F1PlaneLine.value (F1PlaneLine.line, .hyperplane) = 0 := by
  rw [F1PlaneLine.hyperplane_eq_frame]
  simp only [shifted_lower_zero, Finset.sum_const_zero, shifted_divisor_zero, zero_div, sub_zero]

/-- The original row checker accepts the complete numerical energy-three grid. -/
theorem accepted : SurfaceGenusTwoBlowupBoundedCertificate.checkTable (X := X) 0 3
    (F1PlaneLine.candidate 0) = true := by
  apply (F1PlaneLine.accepted_iff 0).mpr
  exact hyperplane_value.symm.trans F1PlaneLine.hyperplane_eq_frame

/-- Every canonical value in the new mixed full class is now numerical. -/
theorem line_values (f : Family X) : value (line, f) = 0 := by
  cases f with
  | hyperplane => exact hyperplane_value
  | point => exact point_eq_hyperplane.trans hyperplane_value
  | primary => exact primary_value
  | exceptional i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact exceptional_value

/-- Read the completed 24-state table using the same boundary-valued function as at energy two. -/
theorem values_eq (s : State X) (hs : X.effective.energy s.1 ≤ 3) :
    value s = BlowupF1FiberHReduction.boundary s := by
  unfold value
  rw [← checkTable_sound 0 3 (candidate 0) accepted s hs]
  unfold candidate
  split_ifs with hc
  · obtain ⟨beta,f⟩ := s
    change beta = line at hc
    subst beta
    have hz := SurfaceGenusTwoBlowupBoundary.value_of_ne_zero line (by decide +kernel) f
    cases f <;> exact hz.symm
  · rfl

end AxiomaticGW.F1PlaneLine
