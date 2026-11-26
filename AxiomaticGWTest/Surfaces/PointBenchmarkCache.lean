module

public import AxiomaticGW.Surfaces.PointBenchmarkCache
public import AxiomaticGW.Surfaces.GenusTwoBlowupPointCache

/-! Complete primary backends preserve the exact reconstruction constant at every energy. -/

@[expose] public section

namespace AxiomaticGWTest.Surfaces.PointBenchmarkCache

open AxiomaticGW SurfacePointBenchmarkCache SurfaceGenusTwoBlowupOrder

/-- Certified table reuse gives exactly the original constant for every target and family. -/
theorem cached_scalar_constant {X : SurfaceTarget} (i : Fin X.blowups) (s : State X) :
    SurfaceGenusTwoBlowupPointCache.constant i s (genusZero X) (genusOne X) =
      SurfaceGenusTwoBlowupScalar.constant i s :=
  SurfaceGenusTwoBlowupPointCache.constant_eq i s _ _ (genusZero_eq X) (genusOne_eq X)

/-- Energy thirteen is outside the table and keeps the original rational evaluator. -/
theorem energy_thirteen_rational_fallback :
    genusZero .blowupTwo ![13, 0, 0] = SurfaceGenusZero.pointValue .blowupTwo ![13, 0, 0] := by
  have hb : ¬ SurfaceTarget.blowupTwo.effective.energy ![13, 0, 0] ≤ 12 := by decide +kernel
  rw [genusZero, if_neg hb]

/-- The elliptic branch has the same total fallback, without an unsupported zero answer. -/
theorem energy_thirteen_elliptic_fallback :
    genusOne .blowupTwo ![13, 0, 0] = SurfaceGenusOne.pointValue .blowupTwo ![13, 0, 0] := by
  have hb : ¬ SurfaceTarget.blowupTwo.effective.energy ![13, 0, 0] ≤ 12 := by decide +kernel
  rw [genusOne, if_neg hb]

/-- Distinct complete classes are used as distinct table keys even when their energies match. -/
theorem equal_energy_full_keys :
    genusZero .blowupTwo ![2, 3, 1] =
        SurfaceGenusZero.pointBenchmarkValues .blowupTwo ![2, 3, 1] ∧
      genusOne .blowupTwo ![3, 2, 1] =
        SurfaceGenusOne.pointBenchmarkValues .blowupTwo ![3, 2, 1] := by
  constructor
  · rw [genusZero, if_pos (by decide +kernel)]
  · rw [genusOne, if_pos (by decide +kernel)]

/-- The auxiliary zero-class primary convention is preserved for every fixed target. -/
theorem auxiliary_zero_class (X : SurfaceTarget) :
    genusZero X 0 = SurfaceGenusZero.pointValue X 0 ∧
      genusOne X 0 = SurfaceGenusOne.pointValue X 0 := by
  rw [genusZero_eq, genusOne_eq]
  exact ⟨rfl, rfl⟩

end AxiomaticGWTest.Surfaces.PointBenchmarkCache
