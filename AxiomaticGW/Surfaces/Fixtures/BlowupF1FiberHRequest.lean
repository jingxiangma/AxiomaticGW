/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupScalar

/-!
# The exact first F1 hyperplane request

These full-class and full-query identifiers are shared by the numerical
coefficient proofs and the complete-row reconstruction consumer. They carry
no claimed value and do not import the checked lower-genus constant.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberHReduction
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder

abbrev target : SurfaceTarget := .hirzebruchOne
abbrev fiber : target.Curve := ![0, 1]
abbrev exceptional : target.Curve := ![1, 0]
abbrev fiberState : State target := (fiber, .hyperplane)
abbrev hZero : Variable target := .inr (Family.hyperplane.query 0)
abbrev kZero : Variable target := .inr ((Family.exceptional 0).query 0)

/-- The actual coefficient of H0 in the complete shifted fiber equation. -/
def hZeroCoefficient : ℚ :=
  SurfaceGenusTwoBlowupScalar.singletonCoefficient 0 fiberState hZero

/-- The actual coefficient of K0 in the same complete shifted fiber equation. -/
def kZeroCoefficient : ℚ :=
  SurfaceGenusTwoBlowupScalar.singletonCoefficient 0 fiberState kZero

end AxiomaticGW.BlowupF1FiberHReduction
