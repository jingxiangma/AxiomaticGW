module

public import AxiomaticGW.Surfaces.GenusTwoBlowupOrder

/-!
# Incoming genus-two GKM values on the strict two-point line

Report SHA256: 784209a77ddcf4ec7bf74ddbcde84c2e654836b405d4621fded5e977cee841a6
The full effective basis is E₁, E₂, H − E₁ − E₂.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoLineCanonical
open SurfaceGenusTwoBlowupOrder

/-- The five incoming requests retain each cotangent power and ordered insertion. -/
def requests : Fin 5 → SurfaceQuery .blowupTwo :=
  ![⟨2, ![0, 0, 1], [⟨.hyperplane, 1⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![0, 0, 1], [⟨.point, 1⟩]⟩,
    ⟨2, ![0, 0, 1], [⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![0, 0, 1], [⟨.exceptional 0, 1⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![0, 0, 1], [⟨.exceptional 1, 1⟩, ⟨.point, 0⟩]⟩]

/-- The ordinary specializations of the incoming equivariant localization functions. -/
def values : Fin 5 → ℚ := ![0, 0, 0, 0, 0]

/-- Canonical families in the order of the request frame. -/
def families : Fin 5 → Family .blowupTwo :=
  ![.hyperplane, .point, .primary, .exceptional 0, .exceptional 1]

/-- Every exchange row matches its full canonical query at the specified curve. -/
theorem coverage (i : Fin 5) : requests i = (families i).query ![0, 0, 1] := by
  fin_cases i <;> decide +kernel

end AxiomaticGW.GKM.BlowupTwoLineCanonical
