/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PrimitiveTaylorTranslation
public import AxiomaticGWTest.GKM.SemisimpleCalibration

/-! # Even and odd translation gauges for the primitive resolvent -/

@[expose] public section
namespace AxiomaticGWTest.GKM.PrimitiveTaylorTranslation
open AxiomaticGW AxiomaticGW.GKM Matrix EquivariantCoefficients
open BlowupQuantumIdempotents (Index Direction)
open AxiomaticGW.GKM.SemisimpleCalibration (presentation)
open AxiomaticGW.GKM.PrimitiveTaylorTranslation

/-- The even coefficient has a nonzero off-diagonal in the plane, while its diagonal vanishes. -/
theorem plane_quadratic :
    offDiagonal .plane 0 2 0 1 = 1 / (y^4 * (x-y)) ∧
      offDiagonal .plane 0 2 0 1 ≠ 0 ∧ offDiagonal .plane 0 2 0 0 = 0 := by
  have h := SemisimpleCalibration.plane_quadratic_taylor
  refine ⟨?_, ?_, rfl⟩
  · simpa only [offDiagonal, if_neg (by decide : (0 : Fin 3) ≠ 1)] using h.1
  · simpa only [offDiagonal, if_neg (by decide : (0 : Fin 3) ≠ 1), h.1] using h.2

/-- A nonzero change in the prescribed quadratic row sum violates the parity condition. -/
theorem quadratic_rejects_shift (X : SurfaceTarget) (d : BlowupQuantumIdempotents.Direction X)
    (i : BlowupQuantumIdempotents.Index X) :
    ¬ Admissible X d 2 (offDiagonal X d 2 *ᵥ 1 + Pi.single i 1) := by
  rintro (h | h)
  · exact (by decide : ¬Odd 2) h
  · have hi := congrFun h i
    simp only [Pi.add_apply, Pi.single_eq_same, add_eq_left, one_ne_zero] at hi

/-- The cubic power accepts every translation. Together with the forced quadratic row sum it
gives a finite polynomial preserving the full projector Gram matrix. -/
theorem quadratic_cubic (X : SurfaceTarget)
    (v : Direction X → Index X → Coefficient)
    (z : FirstOrderFixedPoints.Scalars Coefficient (BlowupQuantumIdempotents.Direction X)) :
    let u := fun (m : ℕ) d ↦ if m = 2 then offDiagonal X d 2 *ᵥ 1 else v d
    (1 + correction X {1, 2} u (-z)).transpose * (presentation X).gram *
      (1 + correction X {1, 2} u z) = (presentation X).gram := by
  dsimp only
  apply symplectic
  intro k hk d
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (by decide)
end AxiomaticGWTest.GKM.PrimitiveTaylorTranslation
