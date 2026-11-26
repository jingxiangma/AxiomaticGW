/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.GraphIsomorphisms

set_option linter.privateModule false

/-!
# Graph isomorphism enumeration regressions

These kernel-checked finite computations retain loop branch swaps, repeated
edges, and decoration stabilizers. They do not assert any geometric gluing
degree or relation normalization.
-/

namespace AxiomaticGWTest.Tautological.GraphIsomorphisms

open AxiomaticGW

private def oneLoop : StableGraphCode (Fin 1) where
  vertexCount := 1
  edgeCount := 1
  vertexCount_pos := by decide
  legVertex := fun _ ↦ 0
  endpoint := fun _ _ ↦ 0
  genus := fun _ ↦ 0
  connected := by
    intro v w
    have h : v = w := Subsingleton.elim _ _
    subst w
    exact Relation.ReflTransGen.refl
  stable := by
    intro v
    have h : v = 0 := Subsingleton.elim _ _
    subst v
    decide

private def twoLoops : StableGraphCode (Fin 1) where
  vertexCount := 1
  edgeCount := 2
  vertexCount_pos := by decide
  legVertex := fun _ ↦ 0
  endpoint := fun _ _ ↦ 0
  genus := fun _ ↦ 0
  connected := by
    intro v w
    have h : v = w := Subsingleton.elim _ _
    subst w
    exact Relation.ReflTransGen.refl
  stable := by
    intro v
    have h : v = 0 := Subsingleton.elim _ _
    subst v
    decide

private def decoratedLoop (a b : ℕ) : DecoratedStableGraph (Fin 1) where
  graph := oneLoop
  kappaPower := fun _ ↦ 0
  legPsiPower := fun _ ↦ 0
  halfEdgePsiPower := fun _ ↦ ![a, b]

private def decoratedTwoLoops (a b : ℕ) : DecoratedStableGraph (Fin 1) where
  graph := twoLoops
  kappaPower := fun _ ↦ 0
  legPsiPower := fun _ ↦ 0
  halfEdgePsiPower := fun e _ ↦ ![a, b] e

/-- A computable monomial fixture. Mathlib's general `Finsupp.single`
uses classical equality internally, so it is not a kernel evaluation input. -/
private def kappaMonomial (index power : ℕ+) : ℕ+ →₀ ℕ where
  support := {index}
  toFun i := if i = index then power else 0
  mem_support_toFun i := by
    simp only [Finset.mem_singleton]
    split_ifs with h
    · exact iff_of_true h (Nat.ne_of_gt power.property)
    · exact iff_of_false h (not_not.mpr rfl)

/-- A loop has two branch permutations even though its endpoints coincide. -/
example : oneLoop.automorphismCount = 2 := by decide

/-- Two indistinguishable loops contribute `2! * 2^2` automorphisms. -/
example : twoLoops.automorphismCount = 8 := by decide

/-- Different edge counts cannot be related by an isomorphism. -/
example : StableGraphCode.isomorphic? oneLoop twoLoops = false := by decide

/-- Equal branch powers retain the loop flip; unequal powers break it. -/
example :
    (decoratedLoop 1 1).automorphismCount = 2 ∧
      (decoratedLoop 0 1).automorphismCount = 1 := by
  decide

/-- Exchanging the two powers is nevertheless an isomorphism between
presentations, so branch order is not part of the stratum. -/
example : DecoratedStableGraph.Isomorphic (decoratedLoop 0 1) (decoratedLoop 1 0) := by
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).1
  decide

/-- Changing a power cannot be hidden by branch permutations. -/
example :
    DecoratedStableGraph.isomorphic? (decoratedLoop 0 1) (decoratedLoop 0 2) = false := by
  decide

/-- Repeated decorated edges retain their exchange; different decorations
remove the edge exchange while preserving each loop flip. -/
example :
    (decoratedTwoLoops 1 1).automorphismCount = 8 ∧
      (decoratedTwoLoops 0 1).automorphismCount = 4 := by
  decide

/-- Kappa powers are compared as finitely supported functions, including
indices with the same total codimension but different monomials. -/
example :
    DecoratedStableGraph.isomorphic?
      { decoratedLoop 0 0 with kappaPower := fun _ ↦ kappaMonomial 1 2 }
      { decoratedLoop 0 0 with kappaPower := fun _ ↦ kappaMonomial 2 1 } = false := by
  decide

/-- External psi powers remain attached to their fixed labels. -/
example :
    DecoratedStableGraph.isomorphic? (decoratedLoop 0 0)
      { decoratedLoop 0 0 with legPsiPower := fun _ ↦ 1 } = false := by
  decide

/-- The boolean certificate also proves equality in the existing quotient
of decorated presentations. -/
example :
    TautologicalStratum.mk (decoratedLoop 0 1) (by decide : oneLoop.totalGenus = 1) =
      TautologicalStratum.mk (decoratedLoop 1 0) (by decide : oneLoop.totalGenus = 1) := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  decide

end AxiomaticGWTest.Tautological.GraphIsomorphisms
