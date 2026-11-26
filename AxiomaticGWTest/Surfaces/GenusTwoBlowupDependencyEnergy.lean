/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupDependencyEnergy

/-! Consumers of actual canonical dependency bounds; no full numerical row is evaluated. -/

@[expose] public section
namespace AxiomaticGWTest.Surfaces.GenusTwoBlowupDependencyEnergy
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
  SurfaceGenusTwoBlowupDependencyEnergy

set_option maxRecDepth 20000

/-- A bound on the target propagates to every surviving canonical coefficient
of its actual complete row, without changing the full class or family. -/
theorem dependencies_stay_within_bound (X : SurfaceTarget) (i : Fin X.blowups)
    (s t : State X) (B : ℕ) (hp : 0 < X.planeDegree s.1)
    (hB : X.effective.energy s.1 ≤ B)
    (hc : RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row i s)
      {.inr (t.2.query t.1)} ≠ 0) : X.effective.energy t.1 ≤ B :=
  (dependency_energy_le_of_positive_planeDegree i s t hp hc).trans hB

/-- A canonical column above the target energy is zero in the complete row,
including both shifted and unshifted equation families. -/
theorem larger_energy_coefficient_zero (X : SurfaceTarget) (i : Fin X.blowups)
    (s t : State X) (hp : 0 < X.planeDegree s.1)
    (he : X.effective.energy s.1 < X.effective.energy t.1) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row i s)
      {.inr (t.2.query t.1)} = 0 := by
  by_contra hc
  have h := dependency_energy_le_of_positive_planeDegree i s t hp hc
  omega

/-- The nonzero actual N pivot occurs at the target energy itself;
the coefficient energy bound therefore cannot be made strict. -/
theorem primary_pivot_at_target_energy (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (hp : 0 < X.planeDegree beta) :
    ∃ t : State X, X.effective.energy t.1 = X.effective.energy beta ∧
      RationalTerms.coefficient
        (SurfaceGenusTwoBlowupRecursion.row i (beta, .primary))
        {.inr (t.2.query t.1)} ≠ 0 := by
  refine ⟨(beta, .primary), rfl, ?_⟩
  change RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
    {.inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))} ≠ 0
  rw [SurfaceGenusTwoBlowupNCoefficients.row_primary_coefficient]
  exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp))

/-- Strictly earlier dependencies can also have the target's energy:
the actual coefficient of H_beta in the complete P row is eighteen. -/
theorem earlier_h_dependency_at_same_energy (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (he : 0 < X.effective.energy beta) :
    Earlier X (beta, .hyperplane) (beta, .point) ∧
      RationalTerms.coefficient
        (SurfaceGenusTwoBlowupRecursion.row i (beta, .point))
        {.inr (Family.hyperplane.query beta)} ≠ 0 := by
  constructor
  · exact earlier_of_rank_lt X _ _ le_rfl (by change 0 < 1; decide)
  · have hc := SurfaceGenusTwoBlowupPCoefficients.hyperplane_coefficient beta he
    change RationalTerms.coefficient
      (SurfaceGenusTwoBlowupRecursion.row i (beta, .point))
      {.inr (Family.hyperplane.query beta)} = 18 at hc
    rw [hc]
    norm_num

/-- The signed-multiplicity class H+E on F1 retains the same bound for every
source family and requested family. Only its plane degree and energies reduce. -/
theorem signed_f1_larger_class_rejected (f g : Family .hirzebruchOne) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row
      (X := .hirzebruchOne) 0 (![2, 1], f))
      {.inr (g.query ![3, 1])} = 0 := by
  apply larger_energy_coefficient_zero .hirzebruchOne 0 (![2, 1], f) (![3, 1], g)
  · change 0 < SurfaceTarget.hirzebruchOne.planeDegree ![2, 1]
    decide +kernel
  · change SurfaceTarget.hirzebruchOne.effective.energy ![2, 1] <
      SurfaceTarget.hirzebruchOne.effective.energy ![3, 1]
    decide +kernel

/-- Both negative signed exceptional multiplicities are retained on Bl2.
A larger-energy foreign exceptional class cannot contribute to an Ei-shifted row. -/
theorem signed_foreign_bl2_larger_class_rejected (f g : Family .blowupTwo) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row
      (X := .blowupTwo) 0 (![2, 3, 1], f))
      {.inr (g.query ![2, 4, 1])} = 0 := by
  apply larger_energy_coefficient_zero .blowupTwo 0 (![2, 3, 1], f) (![2, 4, 1], g)
  · change 0 < SurfaceTarget.blowupTwo.planeDegree ![2, 3, 1]
    decide +kernel
  · change SurfaceTarget.blowupTwo.effective.energy ![2, 3, 1] <
      SurfaceTarget.blowupTwo.effective.energy ![2, 4, 1]
    decide +kernel

end AxiomaticGWTest.Surfaces.GenusTwoBlowupDependencyEnergy
