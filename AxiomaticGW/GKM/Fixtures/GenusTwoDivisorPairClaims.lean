module

public import AxiomaticGW.Surfaces.Queries

/-!
# Native genus-two divisor-pair claims

Report SHA256: c0e0600243ca2ab7b956b20497407a29a79621abfd3b925911e191d04e2549e4
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoDivisorPairs

namespace Plane

/-- Each complete ordered localization request. -/
def requests : Fin 3 → Fin 1 → Fin 2 → SurfaceQuery .plane :=
  ![![![⟨2, ![1], [⟨.hyperplane, 0⟩, ⟨.unit, 5⟩]⟩,
        ⟨2, ![1], [⟨.unit, 5⟩, ⟨.hyperplane, 0⟩]⟩]],
    ![![⟨2, ![1], [⟨.hyperplane, 0⟩, ⟨.hyperplane, 4⟩]⟩,
        ⟨2, ![1], [⟨.hyperplane, 4⟩, ⟨.hyperplane, 0⟩]⟩]],
    ![![⟨2, ![1], [⟨.hyperplane, 0⟩, ⟨.point, 3⟩]⟩,
        ⟨2, ![1], [⟨.point, 3⟩, ⟨.hyperplane, 0⟩]⟩]]]

/-- Ordinary specialization at both marking orders. -/
def values : Fin 3 → Fin 1 → Fin 2 → ℚ :=
  ![![![(13 / 1920), (13 / 1920)]],
    ![![(-1 / 192), (-1 / 192)]],
    ![![(-1 / 240), (-1 / 240)]]]

end Plane

namespace OneBlowup

/-- Each complete ordered localization request. -/
def requests : Fin 4 → Fin 2 → Fin 2 → SurfaceQuery .hirzebruchOne :=
  ![![![⟨2, ![1, 0], [⟨.hyperplane, 0⟩, ⟨.unit, 3⟩]⟩,
        ⟨2, ![1, 0], [⟨.unit, 3⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![1, 0], [⟨.exceptional 0, 0⟩, ⟨.unit, 3⟩]⟩,
        ⟨2, ![1, 0], [⟨.unit, 3⟩, ⟨.exceptional 0, 0⟩]⟩]],
    ![![⟨2, ![1, 0], [⟨.hyperplane, 0⟩, ⟨.hyperplane, 2⟩]⟩,
        ⟨2, ![1, 0], [⟨.hyperplane, 2⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![1, 0], [⟨.exceptional 0, 0⟩, ⟨.hyperplane, 2⟩]⟩,
        ⟨2, ![1, 0], [⟨.hyperplane, 2⟩, ⟨.exceptional 0, 0⟩]⟩]],
    ![![⟨2, ![1, 0], [⟨.hyperplane, 0⟩, ⟨.exceptional 0, 2⟩]⟩,
        ⟨2, ![1, 0], [⟨.exceptional 0, 2⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![1, 0], [⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 2⟩]⟩,
        ⟨2, ![1, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 0⟩]⟩]],
    ![![⟨2, ![1, 0], [⟨.hyperplane, 0⟩, ⟨.point, 1⟩]⟩,
        ⟨2, ![1, 0], [⟨.point, 1⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![1, 0], [⟨.exceptional 0, 0⟩, ⟨.point, 1⟩]⟩,
        ⟨2, ![1, 0], [⟨.point, 1⟩, ⟨.exceptional 0, 0⟩]⟩]]]

/-- Ordinary specialization at both marking orders. -/
def values : Fin 4 → Fin 2 → Fin 2 → ℚ :=
  ![![![0, 0], ![(-5 / 576), (-5 / 576)]],
    ![![0, 0], ![0, 0]],
    ![![0, 0], ![(1 / 240), (1 / 240)]],
    ![![0, 0], ![0, 0]]]

end OneBlowup

namespace TwoBlowups

/-- Each complete ordered localization request. -/
def requests : Fin 10 → Fin 3 → Fin 2 → SurfaceQuery .blowupTwo :=
  ![![![⟨2, ![1, 0, 0], [⟨.hyperplane, 0⟩, ⟨.unit, 3⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.unit, 3⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![1, 0, 0], [⟨.exceptional 0, 0⟩, ⟨.unit, 3⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.unit, 3⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![1, 0, 0], [⟨.exceptional 1, 0⟩, ⟨.unit, 3⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.unit, 3⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![1, 0, 0], [⟨.hyperplane, 0⟩, ⟨.hyperplane, 2⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.hyperplane, 2⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![1, 0, 0], [⟨.exceptional 0, 0⟩, ⟨.hyperplane, 2⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.hyperplane, 2⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![1, 0, 0], [⟨.exceptional 1, 0⟩, ⟨.hyperplane, 2⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.hyperplane, 2⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![1, 0, 0], [⟨.hyperplane, 0⟩, ⟨.exceptional 0, 2⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.exceptional 0, 2⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![1, 0, 0], [⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 2⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![1, 0, 0], [⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 2⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![1, 0, 0], [⟨.hyperplane, 0⟩, ⟨.exceptional 1, 2⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.exceptional 1, 2⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![1, 0, 0], [⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 2⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.exceptional 1, 2⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![1, 0, 0], [⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 2⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.exceptional 1, 2⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![1, 0, 0], [⟨.hyperplane, 0⟩, ⟨.point, 1⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.point, 1⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![1, 0, 0], [⟨.exceptional 0, 0⟩, ⟨.point, 1⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.point, 1⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![1, 0, 0], [⟨.exceptional 1, 0⟩, ⟨.point, 1⟩]⟩,
        ⟨2, ![1, 0, 0], [⟨.point, 1⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![0, 1, 0], [⟨.hyperplane, 0⟩, ⟨.unit, 3⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.unit, 3⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![0, 1, 0], [⟨.exceptional 0, 0⟩, ⟨.unit, 3⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.unit, 3⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![0, 1, 0], [⟨.exceptional 1, 0⟩, ⟨.unit, 3⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.unit, 3⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![0, 1, 0], [⟨.hyperplane, 0⟩, ⟨.hyperplane, 2⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.hyperplane, 2⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![0, 1, 0], [⟨.exceptional 0, 0⟩, ⟨.hyperplane, 2⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.hyperplane, 2⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![0, 1, 0], [⟨.exceptional 1, 0⟩, ⟨.hyperplane, 2⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.hyperplane, 2⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![0, 1, 0], [⟨.hyperplane, 0⟩, ⟨.exceptional 0, 2⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.exceptional 0, 2⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![0, 1, 0], [⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 2⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![0, 1, 0], [⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 2⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![0, 1, 0], [⟨.hyperplane, 0⟩, ⟨.exceptional 1, 2⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.exceptional 1, 2⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![0, 1, 0], [⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 2⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.exceptional 1, 2⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![0, 1, 0], [⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 2⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.exceptional 1, 2⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![0, 1, 0], [⟨.hyperplane, 0⟩, ⟨.point, 1⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.point, 1⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![0, 1, 0], [⟨.exceptional 0, 0⟩, ⟨.point, 1⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.point, 1⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![0, 1, 0], [⟨.exceptional 1, 0⟩, ⟨.point, 1⟩]⟩,
        ⟨2, ![0, 1, 0], [⟨.point, 1⟩, ⟨.exceptional 1, 0⟩]⟩]]]

/-- Ordinary specialization at both marking orders. -/
def values : Fin 10 → Fin 3 → Fin 2 → ℚ :=
  ![![![0, 0], ![(-5 / 576), (-5 / 576)], ![0, 0]],
    ![![0, 0], ![0, 0], ![0, 0]],
    ![![0, 0], ![(1 / 240), (1 / 240)], ![0, 0]],
    ![![0, 0], ![0, 0], ![0, 0]],
    ![![0, 0], ![0, 0], ![0, 0]],
    ![![0, 0], ![0, 0], ![(-5 / 576), (-5 / 576)]],
    ![![0, 0], ![0, 0], ![0, 0]],
    ![![0, 0], ![0, 0], ![0, 0]],
    ![![0, 0], ![0, 0], ![(1 / 240), (1 / 240)]],
    ![![0, 0], ![0, 0], ![0, 0]]]

end TwoBlowups

namespace StrictLine

/-- Each complete ordered localization request. -/
def requests : Fin 5 → Fin 3 → Fin 2 → SurfaceQuery .blowupTwo :=
  ![![![⟨2, ![0, 0, 1], [⟨.hyperplane, 0⟩, ⟨.unit, 3⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.unit, 3⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![0, 0, 1], [⟨.exceptional 0, 0⟩, ⟨.unit, 3⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.unit, 3⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![0, 0, 1], [⟨.exceptional 1, 0⟩, ⟨.unit, 3⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.unit, 3⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![0, 0, 1], [⟨.hyperplane, 0⟩, ⟨.hyperplane, 2⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.hyperplane, 2⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![0, 0, 1], [⟨.exceptional 0, 0⟩, ⟨.hyperplane, 2⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.hyperplane, 2⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![0, 0, 1], [⟨.exceptional 1, 0⟩, ⟨.hyperplane, 2⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.hyperplane, 2⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![0, 0, 1], [⟨.hyperplane, 0⟩, ⟨.exceptional 0, 2⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.exceptional 0, 2⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![0, 0, 1], [⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 2⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![0, 0, 1], [⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 2⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.exceptional 0, 2⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![0, 0, 1], [⟨.hyperplane, 0⟩, ⟨.exceptional 1, 2⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.exceptional 1, 2⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![0, 0, 1], [⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 2⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.exceptional 1, 2⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![0, 0, 1], [⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 2⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.exceptional 1, 2⟩, ⟨.exceptional 1, 0⟩]⟩]],
    ![![⟨2, ![0, 0, 1], [⟨.hyperplane, 0⟩, ⟨.point, 1⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.point, 1⟩, ⟨.hyperplane, 0⟩]⟩],
      ![⟨2, ![0, 0, 1], [⟨.exceptional 0, 0⟩, ⟨.point, 1⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.point, 1⟩, ⟨.exceptional 0, 0⟩]⟩],
      ![⟨2, ![0, 0, 1], [⟨.exceptional 1, 0⟩, ⟨.point, 1⟩]⟩,
        ⟨2, ![0, 0, 1], [⟨.point, 1⟩, ⟨.exceptional 1, 0⟩]⟩]]]

/-- Ordinary specialization at both marking orders. -/
def values : Fin 5 → Fin 3 → Fin 2 → ℚ :=
  ![![![(5 / 576), (5 / 576)], ![(5 / 576), (5 / 576)], ![(5 / 576), (5 / 576)]],
    ![![(1 / 240), (1 / 240)], ![(1 / 240), (1 / 240)], ![(1 / 240), (1 / 240)]],
    ![![(1 / 240), (1 / 240)], ![(1 / 240), (1 / 240)], ![(1 / 240), (1 / 240)]],
    ![![(1 / 240), (1 / 240)], ![(1 / 240), (1 / 240)], ![(1 / 240), (1 / 240)]],
    ![![0, 0], ![0, 0], ![0, 0]]]

end StrictLine

end AxiomaticGW.GKM.GenusTwoDivisorPairs
