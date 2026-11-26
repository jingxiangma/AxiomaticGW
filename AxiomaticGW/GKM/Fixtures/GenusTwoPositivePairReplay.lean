/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoPositivePairClaims
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPositiveDivisorPairs
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPrimitiveDivisorProduct
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Assembly

/-! # Native replay for two positive cotangent powers in genus two

The ordered query and its exact ordinary specialization are checked against
the original mixed-cotangent evaluator.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoPositivePairs
open SurfaceGenusTwoBlowupDescendants

/-- Both E insertions at the primitive F₁ exceptional class carry one cotangent power. -/
theorem OneBlowup.exceptional_accepted :
    queryValue? 0 (OneBlowup.requests 2 2) = some (OneBlowup.values 2 2) := by
  exact SurfaceGenusTwoPositiveDivisorPairs.HirzebruchOne.exceptionalPair_value

private theorem compare {X : SurfaceTarget} (i : Fin X.blowups) (beta : X.Curve)
    (a b : SurfaceBasisLabel X) (q : SurfaceQuery X) (claimed : ℚ)
    (he : X.effective.energy beta = 1) (hp : SurfaceGenusTwoBlowupRecursion.values i
      (beta, .point) = 0) (ha : a.codimension = 1) (hb : b.codimension = 1)
    (hq : q = ⟨2, beta, [⟨a, 1⟩, ⟨b, 1⟩]⟩)
    (hv : a.primaryFactor beta * b.primaryFactor beta / 144 = claimed) :
    queryValue? i q = some claimed := by
  rw [hq, SurfaceGenusTwo.queryValue?_primitiveDivisorProduct i beta he a b ha hb, hp,
    mul_zero, add_zero, hv]

private def f1Divisor : Fin 2 → SurfaceBasisLabel .hirzebruchOne := ![.hyperplane, .exceptional 0]
private def bl2Divisor : Fin 3 → SurfaceBasisLabel .blowupTwo :=
  ![.hyperplane, .exceptional 0, .exceptional 1]

/-- All four F₁ divisor products, including both mixed orders at the exceptional class. -/
theorem OneBlowup.divisors_accepted (j k : Fin 2) :
    queryValue? 0 (OneBlowup.requests j.succ k.succ) = some (OneBlowup.values j.succ k.succ) := by
  let beta := BlowupF1ExceptionalOneMarkingRequest.exceptional
  have hp : SurfaceGenusTwoBlowupRecursion.values 0 (beta, .point) = 0 := by
    rw [SurfaceGenusTwoBlowupRecursion.values_boundary _ _ (by decide +kernel)]
    decide +kernel
  apply compare 0 beta (f1Divisor j) (f1Divisor k) _ _ (by decide +kernel) hp
  all_goals revert j k; decide +kernel

/-- All nine ordered first-divisor products at the first exceptional class. -/
theorem ExceptionalOne.divisors_accepted (j k : Fin 3) :
    queryValue? 0 (ExceptionalOne.requests j.succ k.succ) =
      some (ExceptionalOne.values j.succ k.succ) := by
  let beta : SurfaceTarget.blowupTwo.Curve := ![1, 0, 0]
  have hp : SurfaceGenusTwoBlowupRecursion.values 0 (beta, .point) = 0 := by
    rw [BlowupTwoLineTable.values_eq _ (by decide +kernel)]
    decide +kernel
  apply compare 0 beta (bl2Divisor j) (bl2Divisor k) _ _ (by decide +kernel) hp
  all_goals revert j k; decide +kernel

/-- All nine ordered first-divisor products at the second exceptional class. -/
theorem ExceptionalTwo.divisors_accepted (j k : Fin 3) :
    queryValue? 0 (ExceptionalTwo.requests j.succ k.succ) =
      some (ExceptionalTwo.values j.succ k.succ) := by
  let beta : SurfaceTarget.blowupTwo.Curve := ![0, 1, 0]
  have hp : SurfaceGenusTwoBlowupRecursion.values 0 (beta, .point) = 0 := by
    rw [BlowupTwoLineTable.values_eq _ (by decide +kernel)]
    decide +kernel
  apply compare 0 beta (bl2Divisor j) (bl2Divisor k) _ _ (by decide +kernel) hp
  all_goals revert j k; decide +kernel

/-- All nine ordered first-divisor products at the strict transform of the line. -/
theorem StrictLine.divisors_accepted (j k : Fin 3) :
    queryValue? 0 (StrictLine.requests j.succ k.succ) = some (StrictLine.values j.succ k.succ) := by
  let beta : SurfaceTarget.blowupTwo.Curve := ![0, 0, 1]
  have hp : SurfaceGenusTwoBlowupRecursion.values 0 (beta, .point) = 0 := by
    rw [BlowupTwoLineTable.values_eq _ (by decide +kernel)]
    decide +kernel
  apply compare 0 beta (bl2Divisor j) (bl2Divisor k) _ _ (by decide +kernel) hp
  all_goals revert j k; decide +kernel

end AxiomaticGW.GKM.GenusTwoPositivePairs
