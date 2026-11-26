/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupOrder
import AxiomaticGW.Surfaces.GenusTwoBlowupHPivots

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoBlowupOrder
open AxiomaticGW SurfaceGenusTwoBlowupOrder

-- Reducible effective H + E retains a negative signed exceptional multiplicity.
example : SurfaceTarget.hirzebruchOne.planeDegree ![2, 1] = 1 := by decide +kernel

example : SurfaceTarget.hirzebruchOne.signedMultiplicity ![2, 1] 0 = -1 := by
  decide +kernel

example : SurfaceTarget.hirzebruchOne.signedMultiplicity ![3, 1] 0 = -2 := by
  decide +kernel

-- Shifting by E₁ preserves the distinct E₂ coordinate, even at negative alpha₁.
example : SurfaceTarget.blowupTwo.signedMultiplicity ![3, 1, 1] 0 = -2 := by
  decide +kernel

example : SurfaceTarget.blowupTwo.signedMultiplicity ![3, 1, 1] 1 = 0 := by
  decide +kernel

-- Degree zero permits arbitrary mixtures of exceptional generators.
example : (![4, 7, 0] : SurfaceTarget.blowupTwo.Curve) =
    4 • SurfaceTarget.blowupTwo.exceptionalCurve 0 +
      7 • SurfaceTarget.blowupTwo.exceptionalCurve 1 := by decide +kernel

example (X : SurfaceTarget) (beta : X.Curve) (hd : X.planeDegree beta = 0) :
    beta = ∑ i : Fin X.blowups, beta i.castSucc • X.exceptionalCurve i :=
  X.eq_sum_exceptionalCurve_of_planeDegree_eq_zero beta hd

-- This is precisely the existing exceptional point-support premise.
example (X : SurfaceTarget) (beta : X.Curve) (hd : X.planeDegree beta = 0) :
    X.divisorIntersections beta 0 = 0 :=
  (X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero beta).mp hd

-- The actual shifted-H request preserves hyperplane degree despite higher energy.
example (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve) :
    X.planeDegree (SurfaceGenusTwoBlowupHPivots.sourceCurve X i beta) =
      X.planeDegree beta :=
  X.planeDegree_add_exceptionalCurve beta i

example : Earlier .hirzebruchOne (![1, 1], .hyperplane) (![0, 1], .primary) := by
  rw [earlier_iff]
  decide +kernel

example : SurfaceTarget.hirzebruchOne.effective.energy ![0, 1] <
    SurfaceTarget.hirzebruchOne.effective.energy ![1, 1] := by decide +kernel

-- Removing E₂ from the shifted E₂ + E₁ source leaves E₁ at the same measure.
-- Full equation support must rule out or solve this dependency separately.
example : (![1, 0, 0] : SurfaceTarget.blowupTwo.Curve) + ![0, 1, 0] =
    ![0, 1, 0] + SurfaceTarget.blowupTwo.exceptionalCurve 0 := by decide +kernel

example : ¬Earlier .blowupTwo (![1, 0, 0], .hyperplane) (![0, 1, 0], .hyperplane) := by
  rw [earlier_iff]
  decide +kernel

example : (Family.hyperplane : Family .blowupTwo).query ![1, 0, 0] ≠
    (Family.hyperplane : Family .blowupTwo).query ![0, 1, 0] := by decide +kernel

-- This obstruction also occurs at positive plane degree, outside the exceptional base.
example : (![1, 0, 1] : SurfaceTarget.blowupTwo.Curve) + ![0, 1, 0] =
    ![0, 1, 1] + SurfaceTarget.blowupTwo.exceptionalCurve 0 := by decide +kernel

example : ¬Earlier .blowupTwo (![1, 0, 1], .hyperplane) (![0, 1, 1], .hyperplane) := by
  rw [earlier_iff]
  decide +kernel

example : (Family.hyperplane : Family .blowupTwo).query ![1, 0, 1] ≠
    (Family.hyperplane : Family .blowupTwo).query ![0, 1, 1] := by decide +kernel

-- Positive-degree remainder lowers the outer degree even at remainder energy one.
example : Earlier .blowupTwo (![3, 0, 0], .hyperplane) (![2, 0, 1], .hyperplane) := by
  rw [earlier_iff]
  decide +kernel

example (X : SurfaceTarget) (i : Fin X.blowups) (f : Family X)
    (beta gamma delta : X.Curve) (h : gamma + delta = beta + X.exceptionalCurve i) :
    Earlier X (gamma, f) (beta, f) ↔
      0 < X.planeDegree delta ∨ 1 < X.effective.energy delta :=
  earlier_shifted_same_family_iff X i f h

-- The order is well-founded on the whole coordinate monoid, with no alpha >= 0 condition.
example (X : SurfaceTarget) : WellFounded (Earlier X) := earlier_wellFounded X

-- Every normalized canonical request retains a state at its own full curve class.
example (X : SurfaceTarget) (beta : X.Curve) (q : SurfaceQuery X)
    (hq : q ∈ SurfaceGenusTwo.canonicalQueries X beta) :
    ∃ f : Family X, f.query beta = q := family_of_mem_canonicalQueries hq

/-- Full equal-measure shifted dependencies have an actual exceptional remainder. -/
public theorem shifted_equal_measure_remainder (X : SurfaceTarget) (i : Fin X.blowups)
    (beta gamma delta : X.Curve) (h : gamma + delta = beta + X.exceptionalCurve i)
    (hd : X.planeDegree gamma = X.planeDegree beta)
    (he : X.effective.energy gamma = X.effective.energy beta) :
    ∃ j : Fin X.blowups, delta = X.exceptionalCurve j :=
  X.exceptional_remainder_of_shifted_same_planeDegree_and_energy i h hd he

/-- An energy-one strict line is excluded by the degree-zero hypothesis. -/
public theorem strict_line_not_exceptional :
    SurfaceTarget.blowupTwo.effective.energy ![0, 0, 1] = 1 ∧
      SurfaceTarget.blowupTwo.planeDegree ![0, 0, 1] ≠ 0 := by
  decide +kernel

/-- The classifier retains the other generator instead of conflating energies. -/
public theorem other_generator_classified :
    ∃ j : Fin SurfaceTarget.blowupTwo.blowups,
      (![0, 1, 0] : SurfaceTarget.blowupTwo.Curve) =
        SurfaceTarget.blowupTwo.exceptionalCurve j ∧ j ≠ 0 := by
  exact ⟨1, by decide +kernel, by decide +kernel⟩

end AxiomaticGWTest.Surfaces.GenusTwoBlowupOrder
