module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineOneMarking

/-!
# Native GKM one-marked descendants at the Bl2 strict line

Report SHA256: 16b54661cae386da219c4f60f27e2f437f599a2f8e5604498c924e75ac3bd45b
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoLineOneMarkingReplay
open BlowupTwoLineBP BlowupTwoLineOneMarking

/-- Requests in the order unit, H, E₁, E₂, point. -/
def requests : Fin 5 → SurfaceQuery .blowupTwo :=
  ![⟨2, ![0, 0, 1], [⟨.unit, 3⟩]⟩,
    ⟨2, ![0, 0, 1], [⟨.hyperplane, 2⟩]⟩,
    ⟨2, ![0, 0, 1], [⟨.exceptional 0, 2⟩]⟩,
    ⟨2, ![0, 0, 1], [⟨.exceptional 1, 2⟩]⟩,
    ⟨2, ![0, 0, 1], [⟨.point, 1⟩]⟩]

/-- Ordinary specialization of each incoming equivariant rational function. -/
def values : Fin 5 → ℚ := ![(13 / 2880), (1 / 240), (1 / 240), (1 / 240), 0]

/-- All four high-power native values agree with the original descendant evaluator. -/
theorem high_accepted (j : Fin 4) :
    SurfaceGenusTwoBlowupDescendants.queryValue? 0 (requests j.castSucc) =
      some (values j.castSucc) := by
  have hq : requests j.castSucc = highRequest j := by fin_cases j <;> decide +kernel
  rw [hq, high_descendants]
  fin_cases j <;> decide +kernel

/-- The native point comparison is equivalent to the remaining canonical H value. -/
theorem point_agrees_iff :
    SurfaceGenusTwoBlowupDescendants.queryValue? 0 (requests 4) = some (values 4) ↔
      SurfaceGenusTwoBlowupRecursion.values 0 (line, .hyperplane) = 0 := by
  rw [show requests 4 = pointRequest by decide +kernel, point_descendant]
  exact Option.some_inj

end AxiomaticGW.GKM.BlowupTwoLineOneMarkingReplay
