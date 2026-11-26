/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinements
public import AxiomaticGW.GKM.Fixtures.HodgeNodeNormal
public import Mathlib.Tactic.Module

/-!
# Bind the finite loop refinements to five original Hodge-packet slots

Only finite contraction-pair orbit counts and the already constructed signed
node expression are used. This does not identify the expression with a square
in cohomology. A geometric pull-push/excess comparison remains necessary.
Both differently presented parallel graphs retain their original coefficients.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.LoopSquarePacketBinding

open AdmcyclesHodgeStrataCandidates
open LoopSquareRefinements

/-- The second original parallel presentation represents the same graph class. -/
theorem rawGraph31_eq_rawGraph28 : rawGraph31 = rawGraph28 := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Coefficients come from the actual finite orbit enumeration. This is an
explicit strata expression, with no claim that it is a geometric product. -/
noncomputable def refinementExpression : StrataModule 2 (Fin 1) :=
  ((orbits target).card : ℚ) • StrataModule.nonseparatingNodeNormal
      (StrataModule.basis HodgeNodeNormal.source) +
    ((orbits doubleLoop).card : ℚ) • StrataModule.basis rawGraph12 +
    ((orbits parallel).card : ℚ) • StrataModule.basis rawGraph28

/-- Unpack the exact shared-edge and disjoint-edge multiplicities. -/
theorem refinementExpression_eq :
    refinementExpression =
      (2 : ℚ) • StrataModule.nonseparatingNodeNormal
        (StrataModule.basis HodgeNodeNormal.source) +
      StrataModule.basis rawGraph12 + (4 : ℚ) • StrataModule.basis rawGraph28 := by
  rw [refinementExpression, shared_counts.2.2, doubleLoop_counts.2.2,
    parallel_counts.2.2]
  simp only [Nat.cast_ofNat, Nat.cast_one, one_smul]

/-- Retain the original five positions; other packet terms remain outside this claim. -/
noncomputable def packetPart : StrataModule 2 (Fin 1) :=
  raw_1_1_degree2Coordinates 3 • StrataModule.basis (raw_1_1_degree2Columns 3) +
    raw_1_1_degree2Coordinates 4 • StrataModule.basis (raw_1_1_degree2Columns 4) +
    raw_1_1_degree2Coordinates 18 • StrataModule.basis (raw_1_1_degree2Columns 18) +
    raw_1_1_degree2Coordinates 21 • StrataModule.basis (raw_1_1_degree2Columns 21) +
    raw_1_1_degree2Coordinates 23 • StrataModule.basis (raw_1_1_degree2Columns 23)

/-- The actual loop coefficient is 1/24 and all five output coefficients are held. -/
theorem source_coefficients :
    raw_0_1_degree1Columns 2 = rawGraph3 ∧
    raw_0_1_degree1Coordinates 2 = (1 / 24 : ℚ) ∧
    raw_1_1_degree2Coordinates 3 = (-1 / 288 : ℚ) ∧
    raw_1_1_degree2Coordinates 4 = (-1 / 288 : ℚ) ∧
    raw_1_1_degree2Coordinates 18 = (1 / 288 : ℚ) ∧
    raw_1_1_degree2Coordinates 21 = (1 / 288 : ℚ) ∧
    raw_1_1_degree2Coordinates 23 = (1 / 576 : ℚ) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Source-bound equality in the existing free strata module. The expression
constructed by finite enumeration agrees with exactly these five packet slots. -/
theorem packetPart_eq_scaled_refinement :
    packetPart = (1 / 24 : ℚ) ^ 2 • refinementExpression := by
  change (-1 / 288 : ℚ) • StrataModule.basis rawGraph23 +
    (-1 / 288 : ℚ) • StrataModule.basis rawGraph9 +
    (1 / 288 : ℚ) • StrataModule.basis rawGraph28 +
    (1 / 288 : ℚ) • StrataModule.basis rawGraph31 +
    (1 / 576 : ℚ) • StrataModule.basis rawGraph12 = _
  rw [refinementExpression_eq, StrataModule.nonseparatingNodeNormal_basis,
    ← HodgeNodeNormal.rawGraph9_eq_first, ← HodgeNodeNormal.rawGraph23_eq_second,
    rawGraph31_eq_rawGraph28]
  module

end AxiomaticGW.GKM.LoopSquarePacketBinding
