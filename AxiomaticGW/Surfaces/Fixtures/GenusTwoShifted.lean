/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCoefficientRelations
public import AxiomaticGW.Surfaces.PlaneGenusTwoRemainder

/-!
# Kernel replay of two shifted plane BP coefficients

The equation has degree two and five point insertions: the three original
BP labels and two added markings. The requested variable is the degree-one
hyperplane descendant with three primary points. Its coefficient is minus
eighteen. The HPP equation at the same source degree has coefficient minus
thirty-six on the degree-one primary variable. These certify matrix entries,
not invariant values or the complete symbolic matrix.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoShifted
open SurfacePolynomialReduction

/-- The exact degree-one hyperplane-descendant column of the shifted system. -/
def planeLineHyperplane : Variable .plane :=
  .inr (SurfaceFirstDescendant.query 2 ![1] .hyperplane 3)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
-- Allow the closed four-diagram, six-assignment coefficient replay to elaborate.
/-- Closed arithmetic checked by the Lean kernel, with no native decision. -/
theorem planeLineHyperplane_compact :
    BelorousskiPandharipande.pointCoefficient .plane 2 ![2]
      ![.point, .point, .point] planeLineHyperplane = -18 := by
  rw [← BelorousskiPandharipande.planePointCoefficientByRemainder_eq]
  decide +kernel

/-- The certified coefficient belongs to the entire original normalized equation. -/
theorem planeLineHyperplane_full :
    RationalTerms.coefficient (BelorousskiPandharipande.normalizedGenusTwoTerms
      .plane 2 ![2] 0 (SurfaceGenusZero.pointLabels ![.point, .point, .point] 2))
        {planeLineHyperplane} = -18 := by
  rw [← BelorousskiPandharipande.pointCoefficient_eq_full]
  exact planeLineHyperplane_compact

/-- The primary column at degree one, with its complete point multiplicity. -/
def planeLinePrimary : Variable .plane :=
  .inr (SurfaceQuery.points .plane 2 ![1] 4)

private def primaryDiagram (i : Fin 4) : ℚ :=
  BelorousskiPandharipande.rawPaperCoefficient (Fin.castAdd 16 i) *
    ∑ e : Fin 6, SurfaceGenusTwo.remainderPointCoefficient .plane planeLinePrimary
      (SurfaceGenusTwo.planeCoefficientVertex planeLinePrimary)
      (BelorousskiPandharipande.orbitCotangentTerm (Fin.castAdd 16 i) e) ![1] 3
      ![.hyperplane, .point, .point]

section
set_option maxRecDepth 20000

set_option maxHeartbeats 1000000 in
-- Replay one six-assignment diagram with its signed point corrections.
private theorem primaryDiagram_zero : primaryDiagram 0 = -12 := by decide +kernel
set_option maxHeartbeats 1000000 in
-- Replay one six-assignment diagram with its signed point corrections.
private theorem primaryDiagram_one : primaryDiagram 1 = 0 := by decide +kernel
set_option maxHeartbeats 1000000 in
-- Replay one six-assignment diagram with its signed point corrections.
private theorem primaryDiagram_two : primaryDiagram 2 = 18 := by decide +kernel
set_option maxHeartbeats 1000000 in
-- Replay one six-assignment diagram with its signed point corrections.
private theorem primaryDiagram_three : primaryDiagram 3 = -42 := by decide +kernel

end

/-- The shifted HPP row has a nonzero primary coefficient, with all four
genus-two diagrams and all six marking assignments included. -/
theorem planeLinePrimary_compact :
    BelorousskiPandharipande.pointCoefficient .plane 3 ![2]
      ![.hyperplane, .point, .point] planeLinePrimary = -36 := by
  rw [← BelorousskiPandharipande.planePointCoefficientByRemainder_eq]
  change (∑ i : Fin 4, primaryDiagram i) = -36
  rw [Fin.sum_univ_four, primaryDiagram_zero, primaryDiagram_one,
    primaryDiagram_two, primaryDiagram_three]
  norm_num

/-- The nonzero primary coefficient is in the complete normalized BP equation. -/
theorem planeLinePrimary_full :
    RationalTerms.coefficient (BelorousskiPandharipande.normalizedGenusTwoTerms
      .plane 3 ![2] 0 (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] 3))
        {planeLinePrimary} = -36 := by
  rw [← BelorousskiPandharipande.pointCoefficient_eq_full]
  exact planeLinePrimary_compact

end AxiomaticGW.SurfaceGenusTwoShifted
