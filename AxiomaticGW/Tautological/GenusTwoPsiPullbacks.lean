/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GenusTwoPsiForgetful
public import AxiomaticGW.Tautological.CotangentReplay

/-!
# The three fixed higher-arity inputs to genus-two power reduction

These are actual computed pullbacks, not supplied higher-arity relations.
Old markings are first and new markings are appended. Every computed graph
is checked against the independently held two- or three-marked frame.
The incoming Sage coordinates are replayed separately against these terms.
-/

@[expose] public section

namespace AxiomaticGW.GenusTwoPsiPullbacks
open GluingExpression CotangentCombination RelationCertificate

/-- Square relation with one added marking. -/
def squareTwo : CotangentCombination 2 (Fin 2) :=
  (GenusTwoPsiSquare.cotangentRelation.pullback 1).relabel (ExtraMarkings.finEquiv 1 1)

/-- Square relation with two added markings. -/
def squareThree : CotangentCombination 2 (Fin 3) :=
  (GenusTwoPsiSquare.cotangentRelation.pullback 2).relabel (ExtraMarkings.finEquiv 2 1)

/-- Product relation with one added marking. -/
def productThree : CotangentCombination 2 (Fin 3) :=
  (GenusTwoPsiProduct.cotangentRelation.pullback 1).relabel (ExtraMarkings.finEquiv 1 2)

set_option maxRecDepth 10000 in
/-- Lookup succeeds on every actual square pullback term; default matches are not assumed. -/
theorem squareTwo_covered : ∀ t ∈ squareTwo,
    (t.2.expression.decoratedGraph t.2.decoration).isomorphic?
      (GenusTwoPsiProduct.graph (columnIndex GenusTwoPsiProduct.graph t.2)) = true := by
  simp only [GenusTwoPsiProduct.graph,
    BelorousskiPandharipande.tableGraph, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

set_option maxRecDepth 10000 in
/-- The second added marking retains repeated terms and every negative correction. -/
theorem squareThree_covered : ∀ t ∈ squareThree,
    (t.2.expression.decoratedGraph t.2.decoration).isomorphic?
      (BelorousskiPandharipande.graph (columnIndex BelorousskiPandharipande.graph t.2)) = true := by
  simp only [BelorousskiPandharipande.graph,
    BelorousskiPandharipande.tableGraph, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

set_option maxRecDepth 10000 in
/-- Node powers and the same-genus product term remain in the three-marked frame. -/
theorem productThree_covered : ∀ t ∈ productThree,
    (t.2.expression.decoratedGraph t.2.decoration).isomorphic?
      (BelorousskiPandharipande.graph (columnIndex BelorousskiPandharipande.graph t.2)) = true := by
  simp only [BelorousskiPandharipande.graph,
    BelorousskiPandharipande.tableGraph, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Exact interpretation of the complete computed square pullback. -/
theorem squareTwo_strata : squareTwo.strata = interpret GenusTwoPsiProduct.columns
    (coordinates GenusTwoPsiProduct.graph squareTwo) :=
  strata_eq_interpret _ GenusTwoPsiProduct.graph_totalGenus _ squareTwo_covered

/-- Exact interpretation after two successive forgetful pullbacks. -/
theorem squareThree_strata : squareThree.strata = interpret BelorousskiPandharipande.columns
    (coordinates BelorousskiPandharipande.graph squareThree) :=
  strata_eq_interpret _ BelorousskiPandharipande.graph_totalGenus _ squareThree_covered

/-- Exact interpretation of the complete product pullback. -/
theorem productThree_strata : productThree.strata = interpret BelorousskiPandharipande.columns
    (coordinates BelorousskiPandharipande.graph productThree) :=
  strata_eq_interpret _ BelorousskiPandharipande.graph_totalGenus _ productThree_covered

end AxiomaticGW.GenusTwoPsiPullbacks
