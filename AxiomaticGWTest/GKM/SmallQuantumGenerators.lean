/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.OrdinarySmallQuantumGenerators
public import AxiomaticGW.GKM.Fixtures.PlaneQuantumIdempotents

/-! # Source sign, torus weight, curve-label and idempotent regressions -/

@[expose] public section
namespace AxiomaticGWTest.GKM.SmallQuantumGenerators
open AxiomaticGW AxiomaticGW.GKM EquivariantCoefficients

/-- A purely ordinary tensor would discard the nonzero torus-weight term for three point lifts. -/
theorem point_triple_incoming :
    SmallQuantumGeneratorData.plane x y 0 2 2 2 = x - 2*y ∧
    SmallQuantumGeneratorData.plane (1 : ℚ) 0 0 2 2 2 ≠ 0 := by
  constructor
  · change (-2) * y + 1 * x = _
    ring
  · decide +kernel

/-- Equal-energy exceptional generators act differently on the same ordinary pair E₁,E₁.
The next generator L contributes to H*H. -/
theorem full_class_labels :
    OrdinarySmallQuantumGenerators.coefficient .blowupTwo 0 2 2 2 = 1 ∧
    OrdinarySmallQuantumGenerators.coefficient .blowupTwo 1 2 2 2 = 0 ∧
    OrdinarySmallQuantumGenerators.coefficient .blowupTwo 2 1 1 1 = 1 := by decide +kernel

/-- Freezing the accepted fixed-point projectors at degree zero fails for the first projector. -/
theorem frozen_projector_rejected :
    PlaneQuantumIdempotents.linePart (PlaneQuantumIdempotents.projector 0) ≠ 0 :=
  PlaneQuantumIdempotents.projector_zero_moves

end AxiomaticGWTest.GKM.SmallQuantumGenerators
