module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberTable

/-!
# Three incoming genus-two queries on the F1 fiber

Report SHA256: 69a3448d0616f5a4787b550469d3ac442fc24964c1e6735d62ad4444453fd7db
The original canonical reconstruction binds each exact request and ordinary value.
The geometric interpretation uses the original BP/L24 equations and finite seeds.
-/

@[expose] public section

namespace AxiomaticGW.GKM.BlowupF1FiberRemainingReplay
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder BlowupF1FiberHReduction

/-- Incoming genus, full curve and ordered labels with their cotangent powers. -/
def requests : Fin 3 → SurfaceQuery .hirzebruchOne :=
  ![⟨2, ![0, 1], [⟨.point, 1⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![0, 1], [⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![0, 1], [⟨.exceptional 0, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩]

/-- Ordinary specialization of each incoming rational function. -/
def values : Fin 3 → ℚ := ![0, 0, 0]

/-- The independently specified P, N and K canonical families. -/
def families : Fin 3 → Family target := ![.point, .primary, .exceptional 0]

/-- Each request matches its canonical family at the full fiber class. -/
theorem coverage (i : Fin 3) : requests i = (families i).query fiber := by
  fin_cases i <;> decide +kernel

/-- The checked finite reconstruction supplies the ordinary value of each request. -/
theorem accepted (i : Fin 3) :
    canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0) (.inr (requests i)) =
      values i := by
  rw [coverage, canonicalValuation_query, BlowupF1FiberTable.fiber_values]
  fin_cases i <;> norm_num [values]

end AxiomaticGW.GKM.BlowupF1FiberRemainingReplay
