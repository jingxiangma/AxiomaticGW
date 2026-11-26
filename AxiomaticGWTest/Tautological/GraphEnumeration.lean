/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.GraphEnumeration

set_option linter.privateModule false

/-!
# Complete finite stratum enumeration regressions

The corpus is the raw graph-isomorphism quotient. It retains decorations
above a vertex's geometric dimension until a separately justified geometric
vanishing relation removes them. Counts below are of formal strata, not
cohomology dimensions or ranks of relation quotients.
-/

namespace AxiomaticGWTest.Tautological.GraphEnumeration

open AxiomaticGW

set_option maxRecDepth 10000

/-- Only the genus-zero four-point fundamental stratum has codimension zero. -/
example : (TautologicalStratum.boundedStrata (Fin 4) 0 0).card = 1 := by
  simp only [TautologicalStratum.boundedStrata, TautologicalStratum.strataAtSize_eq_semantic,
    StableGraphCode.validCandidates_eq_standard, StableGraphCode.standardCandidates,
    DecoratedStableGraph.decorations_eq_standard, DecoratedStableGraph.toDecoration_eq_mk]
  decide

/-- Four psi classes, kappa_1, and three labelled boundary partitions,
in addition to the fundamental stratum. -/
example : (TautologicalStratum.boundedStrata (Fin 4) 0 1).card = 9 := by
  simp only [TautologicalStratum.boundedStrata, TautologicalStratum.strataAtSize_eq_semantic,
    StableGraphCode.validCandidates_eq_standard, StableGraphCode.standardCandidates,
    DecoratedStableGraph.decorations_eq_standard, DecoratedStableGraph.toDecoration_eq_mk]
  decide

/-- An unstable global arity has no stable graph presentations. -/
example : TautologicalStratum.boundedStrata (Fin 2) 0 1 = ∅ := by
  simp only [TautologicalStratum.boundedStrata, TautologicalStratum.strataAtSize_eq_semantic,
    StableGraphCode.validCandidates_eq_standard, StableGraphCode.standardCandidates,
    DecoratedStableGraph.decorations_eq_standard, DecoratedStableGraph.toDecoration_eq_mk]
  decide

/-- Summed stability forces the three-point genus-zero graph to have one vertex. -/
example (G : StableGraphCode (Fin 3)) (hg : G.totalGenus = 0) :
    G.vertexCount = 1 := by
  have h := G.vertexCount_add_two_le
  simp only [hg, Fintype.card_fin] at h
  have hp := G.vertexCount_pos
  omega

/-- Unmarked genus one is globally unstable, including at larger graph bounds. -/
example : TautologicalStratum.boundedStrata (Fin 0) 1 3 = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x _
  induction x using Quotient.inductionOn with
  | h G =>
    have h := G.1.graph.vertexCount_add_two_le
    rw [G.2, Fintype.card_fin] at h
    have hp := G.1.graph.vertexCount_pos
    omega

/-- Raw syntax retains dimension-zero-factor decorations. Its cardinality
must not be confused with a geometric basis dimension. -/
example : (TautologicalStratum.boundedStrata (Fin 3) 0 1).card = 5 := by
  simp only [TautologicalStratum.boundedStrata, TautologicalStratum.strataAtSize_eq_semantic,
    StableGraphCode.validCandidates_eq_standard, StableGraphCode.standardCandidates,
    DecoratedStableGraph.decorations_eq_standard, DecoratedStableGraph.toDecoration_eq_mk]
  decide

/-- At genus one with one marking, psi, kappa_1, and the nonseparating
boundary remain separate formal generators. -/
example : (TautologicalStratum.boundedStrata (Fin 1) 1 1).card = 4 := by
  simp only [TautologicalStratum.boundedStrata, TautologicalStratum.strataAtSize_eq_semantic,
    StableGraphCode.validCandidates_eq_standard, StableGraphCode.standardCandidates,
    DecoratedStableGraph.decorations_eq_standard, DecoratedStableGraph.toDecoration_eq_mk]
  decide

/-- The unmarked genus-two space has one, three, and eight raw strata in
codimensions zero, one, and two. Its degree-two count matches the pinned
full-stable admcycles fixture. -/
example : (TautologicalStratum.boundedStrata (Fin 0) 2 2).card = 12 := by
  simp only [TautologicalStratum.boundedStrata, TautologicalStratum.strataAtSize_eq_semantic,
    StableGraphCode.validCandidates_eq_standard, StableGraphCode.standardCandidates,
    DecoratedStableGraph.decorations_eq_standard, DecoratedStableGraph.toDecoration_eq_mk]
  decide

example : ((TautologicalStratum.boundedStrata (Fin 0) 2 2).filter
    (fun x ↦ x.codimension = 2)).card = 8 := by
  simp only [TautologicalStratum.boundedStrata, TautologicalStratum.strataAtSize_eq_semantic,
    StableGraphCode.validCandidates_eq_standard, StableGraphCode.standardCandidates,
    DecoratedStableGraph.decorations_eq_standard, DecoratedStableGraph.toDecoration_eq_mk]
  decide

/-- Positive kappa indices are encoded without using noncomputable
`Finsupp.single`; kappa_3 really contributes codimension three. -/
example :
    (DecoratedStableGraph.kappaVector 3 ![0, 0, 1]).sum
      (fun i p ↦ (i : ℕ) * p) = 3 := by decide

/-- Finite decoration search respects kappa weights rather than just the
unweighted sum of exponents. -/
example : (DecoratedStableGraph.decorations (Fin 0) 1 0 3 2).card = 4 := by
  rw [DecoratedStableGraph.decorations_eq_standard]
  decide

/-- Completeness is reusable independently of concrete graph presentations. -/
example {g d : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (x : TautologicalStratum g S) (h : x.codimension ≤ d) :
    x ∈ TautologicalStratum.boundedStrata S g d :=
  (TautologicalStratum.mem_boundedStrata S g d x).2 h

end AxiomaticGWTest.Tautological.GraphEnumeration
