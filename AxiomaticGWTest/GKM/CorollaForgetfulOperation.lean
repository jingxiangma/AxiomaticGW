/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.CorollaForgetful
public import AxiomaticGW.GKM.Fixtures.HodgeKappaSquare

/-! Tests of the retained κ factor, merged index, degree, and actual packet slot. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.CorollaForgetful

open AxiomaticGW AdmcyclesHodgeStrataCandidates

/-- The actual finite pushforward targets position sixteen's graph. -/
theorem actual_packet_column : raw11Degree2Columns 16 = rawGraph21 := rfl

/-- No mixed-term factor two is introduced for this square coefficient. -/
theorem actual_packet_coefficient : raw11Degree2Coordinates 16 = (1 / 144 : ℚ) := rfl

/-- Both output terms are bound to the actual square column and the existing
kappa-two generator, with neither class value supplied. -/
theorem actual_two_term_push :
    CorollaForgetful.push 2 (Fin 1) GKM.HodgeDegreeOneRealization.stable
      (Finsupp.single 1 1) 1 =
      StrataModule.basis rawGraph21 + StrataModule.basis
        (TautologicalStratum.kappaGenerator 2 (Fin 1)
          GKM.HodgeDegreeOneRealization.stable 2) := by
  rw [CorollaForgetful.push_single,
    GKM.HodgeKappaSquare.rawGraph21_eq_kappa_one_squared_corolla,
    ← Finsupp.single_add]
  rfl

/-- Distinct positive κ indices are supported, including empty old markings. -/
theorem distinct_indices_empty_labels :
    CorollaForgetful.push 2 (Fin 0) (by unfold StableArity; decide)
      (Finsupp.single 1 1) 2 =
      StrataModule.basis (TautologicalStratum.oneVertex 2 (Fin 0)
        (by unfold StableArity; decide) (Finsupp.single 1 1 + Finsupp.single 2 1)
        (fun _ ↦ 0)) +
      StrataModule.basis (TautologicalStratum.oneVertex 2 (Fin 0)
        (by unfold StableArity; decide) (Finsupp.single 3 1) (fun _ ↦ 0)) :=
  CorollaForgetful.push_single 2 (Fin 0) (by unfold StableArity; decide) 1 2

/-- A repeated upstairs factor retains its nontrivial binomial coefficient. -/
theorem repeated_factor_multiplicity :
    CorollaForgetful.multiplicity (Finsupp.single 1 2) (Finsupp.single 1 1) = 2 := by
  rw [CorollaForgetful.multiplicity, Finsupp.support_single 1 (by decide : (2 : ℕ) ≠ 0),
    Finset.prod_singleton]
  simp only [Finsupp.single_eq_same]
  decide

end AxiomaticGWTest.GKM.CorollaForgetful
