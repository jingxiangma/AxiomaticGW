module

public import AxiomaticGW.Surfaces.Queries

/-!
# GKM genus-two one-marking claims on the line and exceptional curves

Report SHA256: cba8ce4fcd85491c7244e570db8ac888e5ccb02081f13d68d6c167f4fcd300fd
Each entry preserves the ordinary specialization of the incoming rational function.
The reconstruction comparisons are proved in separate consumers.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoOneMarking

namespace Plane

/-- Full ordered requests from the localization report. -/
def requests : Fin 3 → SurfaceQuery .plane :=
  ![⟨2, ![1], [⟨.unit, 5⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 4⟩]⟩,
    ⟨2, ![1], [⟨.point, 3⟩]⟩]

/-- Ordinary values in the same request order. -/
def values : Fin 3 → ℚ :=
  ![(1 / 128), (-1 / 960), (-1 / 240)]

end Plane

namespace OneBlowup

/-- Full ordered requests from the localization report. -/
def requests : Fin 4 → SurfaceQuery .hirzebruchOne :=
  ![⟨2, ![1, 0], [⟨.unit, 3⟩]⟩,
    ⟨2, ![1, 0], [⟨.hyperplane, 2⟩]⟩,
    ⟨2, ![1, 0], [⟨.exceptional 0, 2⟩]⟩,
    ⟨2, ![1, 0], [⟨.point, 1⟩]⟩]

/-- Ordinary values in the same request order. -/
def values : Fin 4 → ℚ :=
  ![(13 / 2880), 0, (-1 / 240), 0]

end OneBlowup

namespace TwoBlowups

/-- Full ordered requests from the localization report. -/
def requests : Fin 10 → SurfaceQuery .blowupTwo :=
  ![⟨2, ![1, 0, 0], [⟨.unit, 3⟩]⟩,
    ⟨2, ![1, 0, 0], [⟨.hyperplane, 2⟩]⟩,
    ⟨2, ![1, 0, 0], [⟨.exceptional 0, 2⟩]⟩,
    ⟨2, ![1, 0, 0], [⟨.exceptional 1, 2⟩]⟩,
    ⟨2, ![1, 0, 0], [⟨.point, 1⟩]⟩,
    ⟨2, ![0, 1, 0], [⟨.unit, 3⟩]⟩,
    ⟨2, ![0, 1, 0], [⟨.hyperplane, 2⟩]⟩,
    ⟨2, ![0, 1, 0], [⟨.exceptional 0, 2⟩]⟩,
    ⟨2, ![0, 1, 0], [⟨.exceptional 1, 2⟩]⟩,
    ⟨2, ![0, 1, 0], [⟨.point, 1⟩]⟩]

/-- Ordinary values in the same request order. -/
def values : Fin 10 → ℚ :=
  ![(13 / 2880), 0, (-1 / 240), 0, 0, (13 / 2880), 0, 0, (-1 / 240), 0]

end TwoBlowups

end AxiomaticGW.GKM.GenusTwoOneMarking
