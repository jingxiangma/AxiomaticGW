/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GenusTwoPsiPullbacks

/-!
# Incoming exact coordinates of the fixed genus-two psi pullbacks

Input SHA256: 99b712144f5d6bec361f3927865c3592db614aa4fd47a2e8398795c596444232
The graph operations are held independently in GenusTwoPsiPullbacks.
No incoming vector defines its own requested mathematical operation.
-/

@[expose] public section

namespace AxiomaticGW.GenusTwoPsiPullbacksReplay
open CotangentCombination RelationCertificate GenusTwoPsiPullbacks


/-- Exact incoming raw coordinates; every nonprimitive correction is retained. -/
def squareTwoClaim : Coordinates 38 :=
  ![0, 0, 0, 0, 1, 0, 0, 0, -1, 0, (-155 / 351), 0, (-70 / 351), 0, 0, 0, (328 / 1989), (-155 /
    351), (-70 / 351), (155 / 351), (206 / 5967), (-23 / 195), (-23 / 390), 0, (328 / 1989), 0,
    (-7 / 2808), (-31 / 1404), 0, (31 / 1404), (7 / 2808), (-749 / 14040), (-749 / 14040), (-101
    / 477360), (-101 / 477360), (-3 / 1040), (-3 / 1040), (-1 / 56160)]

set_option maxRecDepth 10000 in
/-- Kernel replay compares the vector to the independently computed pullback. -/
theorem squareTwo_checked : coordinates GenusTwoPsiProduct.graph squareTwo =
    squareTwoClaim := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The accepted vector represents the complete actual graph expression. -/
theorem squareTwo_strata : squareTwo.strata =
    interpret GenusTwoPsiProduct.columns squareTwoClaim := by
  rw [GenusTwoPsiPullbacks.squareTwo_strata, squareTwo_checked]

/-- Every nonleading term is a kappa-free boundary with at most one psi factor. -/
theorem squareTwo_reduces : ∀ i, i ≠ 4 → squareTwoClaim i ≠ 0 →
    0 < (GenusTwoPsiProduct.graph i).graph.edgeCount ∧
    (GenusTwoPsiProduct.graph i).kappaCodimension = 0 ∧
    (GenusTwoPsiProduct.graph i).legPsiCodimension +
      (GenusTwoPsiProduct.graph i).halfEdgePsiCodimension ≤ 1 := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Exact incoming raw coordinates; every nonprimitive correction is retained. -/
def squareThreeClaim : Coordinates 100 :=
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1,
    0, (-155 / 351), 0, 0, (-70 / 351), 0, 0, 0, (328 / 1989), (-155 / 351), 0, (-70 / 351), 0,
    0, 0, (328 / 1989), (-155 / 351), 0, (-70 / 351), 0, 0, 0, 0, (328 / 1989), (-155 / 351),
    (-70 / 351), 0, 0, (155 / 351), (155 / 351), (155 / 351), (155 / 351), (155 / 351), (206 /
    5967), (206 / 5967), (206 / 5967), (-23 / 195), (-23 / 195), (-23 / 195), (-23 / 390), (206
    / 5967), (-23 / 195), (206 / 5967), 0, (328 / 1989), 0, (-7 / 2808), (-31 / 1404), 0, 0, 0,
    (31 / 1404), (31 / 1404), (31 / 1404), (7 / 2808), (7 / 2808), (7 / 2808), (-749 / 14040),
    (-749 / 14040), (-749 / 14040), (-749 / 14040), (-101 / 477360), (-101 / 477360), (-101 /
    477360), (-101 / 477360), (-3 / 1040), (-3 / 1040), (-3 / 1040), (-3 / 1040), (-1 / 56160)]

set_option maxRecDepth 10000 in
/-- Kernel replay compares the vector to the independently computed pullback. -/
theorem squareThree_checked : coordinates BelorousskiPandharipande.graph squareThree =
    squareThreeClaim := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The accepted vector represents the complete actual graph expression. -/
theorem squareThree_strata : squareThree.strata =
    interpret BelorousskiPandharipande.columns squareThreeClaim := by
  rw [GenusTwoPsiPullbacks.squareThree_strata, squareThree_checked]

/-- Every nonleading term is a kappa-free boundary with at most one psi factor. -/
theorem squareThree_reduces : ∀ i, i ≠ 5 → squareThreeClaim i ≠ 0 →
    0 < (BelorousskiPandharipande.graph i).graph.edgeCount ∧
    (BelorousskiPandharipande.graph i).kappaCodimension = 0 ∧
    (BelorousskiPandharipande.graph i).legPsiCodimension +
      (BelorousskiPandharipande.graph i).halfEdgePsiCodimension ≤ 1 := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Exact incoming raw coordinates; every nonprimitive correction is retained. -/
def productThreeClaim : Coordinates 100 :=
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, -3, 0, 0,
    3, 0, (161 / 90), (161 / 90), 0, (-40 / 9), 0, 0, 0, (206 / 51), (161 / 90), (161 / 90),
    (-40 / 9), 0, 0, (407 / 180), (-7 / 36), (407 / 180), 0, (-7 / 36), 0, 0, (407 / 180), 0,
    (-7 / 36), (407 / 180), (-7 / 36), (-161 / 90), (-407 / 180), (-161 / 90), (-407 / 180),
    (-25 / 9), (-25 / 9), (-25 / 9), (62 / 153), (-19 / 90), (-19 / 90), (-19 / 90), (-19 / 90),
    (-13 / 15), (-13 / 30), (-19 / 90), (-19 / 90), (7 / 18), 0, (206 / 51), 0, (-7 / 36), (67 /
    720), (67 / 720), 0, (-67 / 720), (-67 / 720), (-11 / 72), (-11 / 72), (7 / 36), (-1 / 40),
    (-1 / 40), (-1 / 40), (-1 / 40), (-37 / 90), (-37 / 90), (473 / 12240), (473 / 12240), (-1 /
    180), (-1 / 180), (-1 / 180), (-1 / 180), (-37 / 720), (-37 / 720), (-1 / 720)]

set_option maxRecDepth 10000 in
/-- Kernel replay compares the vector to the independently computed pullback. -/
theorem productThree_checked : coordinates BelorousskiPandharipande.graph productThree =
    productThreeClaim := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The accepted vector represents the complete actual graph expression. -/
theorem productThree_strata : productThree.strata =
    interpret BelorousskiPandharipande.columns productThreeClaim := by
  rw [GenusTwoPsiPullbacks.productThree_strata, productThree_checked]

/-- Every nonleading term is a kappa-free boundary with at most one psi factor. -/
theorem productThree_reduces : ∀ i, i ≠ 6 → productThreeClaim i ≠ 0 →
    0 < (BelorousskiPandharipande.graph i).graph.edgeCount ∧
    (BelorousskiPandharipande.graph i).kappaCodimension = 0 ∧
    (BelorousskiPandharipande.graph i).legPsiCodimension +
      (BelorousskiPandharipande.graph i).halfEdgePsiCodimension ≤ 1 := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

end AxiomaticGW.GenusTwoPsiPullbacksReplay
