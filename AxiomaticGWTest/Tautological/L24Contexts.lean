/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24HighPsi
public import AxiomaticGW.Tautological.L24RationalPsi
public import AxiomaticGW.Tautological.L24Symmetry
public import AxiomaticGW.Tautological.DecoratedComponentDimension
public import AxiomaticGW.Tautological.GraphIsomorphismHint

/-! # Consequential graph and component-dimension regressions for L24 -/

@[expose] public section

namespace AxiomaticGWTest.L24Contexts
open AxiomaticGW

example : (RationalPsiRelation.size 1, RationalPsiRelation.size 2) = (2, 4) := by
  decide +kernel

/-- The paper's distinguished second marking is fixed in every averaging term. -/
example : ∀ p, L24Symmetry.labels p 1 = 1 := by
  decide +kernel

/-- The six averaging permutations are distinct; no term is silently repeated. -/
example : Function.Injective L24Symmetry.labels := by
  decide +kernel

/-- This node-decorated graph is accepted with its actual ordered identity maps. -/
example : (GraphIsomorphismHint.mk [0, 1] [0] [false]).check
    (GenusTwoPsiProduct.graph 8) (GenusTwoPsiProduct.graph 8) = true := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- An out-of-range index must not be accepted through modular aliasing. -/
example : (GraphIsomorphismHint.mk [2, 1] [0] [false]).check
    (GenusTwoPsiProduct.graph 8) (GenusTwoPsiProduct.graph 8) = false := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Repeated vertices fail bijectivity even though the table has the right length. -/
example : (GraphIsomorphismHint.mk [0, 0] [0] [false]).check
    (GenusTwoPsiProduct.graph 8) (GenusTwoPsiProduct.graph 8) = false := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- A branch exchange cannot move the genus-two node power to the rational component. -/
example : (GraphIsomorphismHint.mk [0, 1] [0] [true]).check
    (GenusTwoPsiProduct.graph 8) (GenusTwoPsiProduct.graph 8) = false := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Kappa decoration cannot be substituted for a node cotangent factor. -/
example : (GraphIsomorphismHint.mk [0, 1] [0] [false]).check
    (GenusTwoPsiProduct.graph 8) (GenusTwoPsiProduct.graph 7) = false := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- An omitted edge branch is rejected, rather than filled by the lookup default. -/
example : (GraphIsomorphismHint.mk [0, 1] [0] []).check
    (GenusTwoPsiProduct.graph 8) (GenusTwoPsiProduct.graph 8) = false := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- A node-decorated rational tail whose global degree is still below the target dimension. -/
def rationalTail : GluingExpression 2 (Fin 2 ⊕ Fin 1) :=
  (GluingExpression.fundamental 0 (Option (Fin 2)) (by norm_num [StableArity])).separating
    (.fundamental 2 (Option (Fin 1)) (by norm_num [StableArity]))

def nodePower : rationalTail.CotangentDecoration :=
  ((fun | none => 1 | some _ => 0), fun _ ↦ 0)

example : rationalTail.exceedsComponentDimension nodePower (fun _ ↦ 0) = true := by
  decide +kernel

example : (rationalTail.decoratedGraph nodePower).codimension = 2 ∧
    2 ≤ StableArity.dimension 2 (Fin 2 ⊕ Fin 1) := by
  decide +kernel

example : rationalTail.exceedsComponentDimension rationalTail.zeroDecoration
    (fun | .inl _ => 1 | .inr _ => 0) = true := by
  decide +kernel

example : rationalTail.exceedsComponentDimension rationalTail.zeroDecoration
    (fun | .inl _ => 0 | .inr _ => 1) = false := by
  decide +kernel

end AxiomaticGWTest.L24Contexts
