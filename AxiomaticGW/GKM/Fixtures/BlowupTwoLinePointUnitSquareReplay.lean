module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Assembly
public import AxiomaticGW.Surfaces.GenusTwoBlowupQueryCertificate

/-!
# The primary point and the second descendant of the unit on the strict line

Report SHA256: b722b147757a49b532933e526a4d335c923916bcc6c2fb7a3be02cfb823adfe3
The full mixed transfer and its pulled-back square are evaluated with the certified
energy-one canonical table, separately for both ordered requests.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoLinePointUnitSquare
open SurfaceGenusTwoBlowupDescendants BlowupTwoLineTable

/-- The native requests retain both marking orders and all strict-line coordinates. -/
def requests : Fin 2 → SurfaceQuery .blowupTwo :=
  ![⟨2, ![0, 0, 1], [⟨.point, 0⟩, ⟨.unit, 2⟩]⟩,
    ⟨2, ![0, 0, 1], [⟨.unit, 2⟩, ⟨.point, 0⟩]⟩]

/-- Ordinary specialization in each order. -/
def values : Fin 2 → ℚ := ![0, 0]

set_option maxRecDepth 65536

set_option maxHeartbeats 1600000 in
-- Each complete mixed expansion includes the universal-curve pullback of the square.
/-- Both ordinary native values agree with the original genus-two descendant evaluator. -/
theorem accepted (o : Fin 2) : queryValue? 0 (requests o) = some (values o) := by
  have he : SurfaceTarget.blowupTwo.effective.energy (requests o).beta ≤ 1 := by
    fin_cases o <;> decide +kernel
  rw [← queryValueWith?_eq 0 1 (candidate 0) BlowupTwoLineTable.accepted _ he]
  fin_cases o <;> decide +kernel

end AxiomaticGW.GKM.BlowupTwoLinePointUnitSquare
