module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroStrataSpecialization

@[expose] public section

namespace AxiomaticGWTest.HodgeDegreeZeroStrataSpecialization
open AxiomaticGW AxiomaticGW.GKM
open HodgeDegreeZeroStrataSpecialization EquivariantCoefficients

/-- The first blowup has multiplier eight on every ordinary graph coordinate. -/
theorem first_blowup_coordinate (s : Stratum) : Specializes (packet .hirzebruchOne s)
    (8 * AdmcyclesHodgeStrataCandidates.raw02Degree2 s) := by
  simpa only [ordinary, SurfaceTarget.blowups, Nat.cast_one, Finsupp.smul_apply,
    smul_eq_mul, show (9 : ℚ) - 1 = 8 by norm_num] using packet_specializes .hirzebruchOne s

/-- Discarding the positive-codimension packet fails the specialization check. -/
theorem rejects_zero (X : SurfaceTarget) : ¬∀ s, Specializes (packet X s) 0 := by
  intro hz
  have he := ordinary_unique X 0 (fun s ↦ hz s)
  exact ordinary_ne_zero X he.symm

end AxiomaticGWTest.HodgeDegreeZeroStrataSpecialization
