/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.Fixtures.GenusTwoPsiPullbacksReplay

open AxiomaticGW CotangentCombination RelationCertificate GenusTwoPsiPullbacks
open GenusTwoPsiPullbacksReplay

-- Old markings stay first; adding two markings does not reverse their order.
example : ExtraMarkings.finEquiv 2 1 (some (some 0)) = 0 ∧
    ExtraMarkings.finEquiv 2 1 (some none) = 1 ∧
    ExtraMarkings.finEquiv 2 1 none = 2 := by decide +kernel

-- Each source is tied to its actual independently computed construction.
example : squareTwo.strata = interpret GenusTwoPsiProduct.columns squareTwoClaim :=
  GenusTwoPsiPullbacksReplay.squareTwo_strata

example : squareThree.strata = interpret BelorousskiPandharipande.columns squareThreeClaim :=
  GenusTwoPsiPullbacksReplay.squareThree_strata

example : productThree.strata = interpret BelorousskiPandharipande.columns productThreeClaim :=
  GenusTwoPsiPullbacksReplay.productThree_strata

-- Pullback produces negative corrections even on the leading smooth component.
example : squareTwoClaim 4 = 1 ∧ squareTwoClaim 8 = -1 := by decide +kernel

-- The old genus-two boundary contributes with a positive tail correction.
example : productThreeClaim 6 = 1 ∧ productThreeClaim 19 = -3 ∧
    productThreeClaim 29 = 3 := by decide +kernel

example : productThreeClaim ≠ squareThreeClaim := by decide +kernel

example (i : Fin 100) (hi : i ≠ 6) (hc : productThreeClaim i ≠ 0) :
    0 < (BelorousskiPandharipande.graph i).graph.edgeCount :=
  (productThree_reduces i hi hc).1

example (n : ℕ) (t : ℚ × GluingExpression.CotangentTerm 2 (ExtraMarkings n (Fin 2)))
    (ht : t ∈ GenusTwoPsiProduct.cotangentRelation.pullback n) :
    (t.2.expression.decoratedGraph t.2.decoration).codimension = 2 :=
  GenusTwoPsiProduct.pulled_term_codimension n t ht

-- A graph absent from a frame cannot be accepted merely through lookup's default index.
set_option maxRecDepth 10000 in
example : ¬ (∀ t ∈ squareTwo,
    (t.2.expression.decoratedGraph t.2.decoration).isomorphic?
      ((fun _ : Fin 1 ↦ GenusTwoPsiProduct.graph 0)
        (columnIndex (fun _ : Fin 1 ↦ GenusTwoPsiProduct.graph 0) t.2)) = true) := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel
