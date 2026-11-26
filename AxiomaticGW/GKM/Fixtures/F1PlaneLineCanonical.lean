module

public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineReduction

/-!
# Incoming canonical genus-two GKM values at H = E + F on the one-point blowup

Report SHA256: e9561079ef7eb5c914757a6fc64e91f03da9348657b318d61ba5f3e996111641
The full effective coordinates are one exceptional curve and one fiber.
-/

@[expose] public section
namespace AxiomaticGW.GKM.F1PlaneLine
open SurfaceGenusTwoBlowupOrder

/-- The four incoming requests retain each cotangent power and ordered insertion. -/
def requests : Fin 4 → SurfaceQuery .hirzebruchOne :=
  ![⟨2, ![1, 1], [⟨.hyperplane, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![1, 1], [⟨.point, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![1, 1], [⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![1, 1], [⟨.exceptional 0, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩]

/-- The ordinary specializations of the incoming equivariant localization functions. -/
def values : Fin 4 → ℚ := ![0, 0, 0, 0]

/-- Every exchange row is the original full canonical query at H = E + F. -/
theorem coverage (i : Fin 4) : requests i =
    (AxiomaticGW.F1PlaneLine.families i).query AxiomaticGW.F1PlaneLine.line := by
  fin_cases i <;> decide +kernel

end AxiomaticGW.GKM.F1PlaneLine
