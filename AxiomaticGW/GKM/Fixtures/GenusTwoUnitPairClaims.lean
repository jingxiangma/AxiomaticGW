module

public import AxiomaticGW.Surfaces.Queries

/-!
# Genus-two two-marked unit claims from the pinned GKM producer

Report SHA256: d936e22a93483961b5b651f4db420730fac5134c69db87e2e15364102f86994d
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoUnitPairs

namespace OneBlowup

/-- Ordered requests in string-first, string-last, dilaton-first, dilaton-last order. -/
def requests : Fin 4 → Fin 4 → SurfaceQuery .hirzebruchOne :=
  ![![⟨2, ![1, 0], [⟨.unit, 0⟩, ⟨.unit, 4⟩]⟩,
      ⟨2, ![1, 0], [⟨.unit, 4⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![1, 0], [⟨.unit, 1⟩, ⟨.unit, 3⟩]⟩,
      ⟨2, ![1, 0], [⟨.unit, 3⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![1, 0], [⟨.unit, 0⟩, ⟨.hyperplane, 3⟩]⟩,
      ⟨2, ![1, 0], [⟨.hyperplane, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![1, 0], [⟨.unit, 1⟩, ⟨.hyperplane, 2⟩]⟩,
      ⟨2, ![1, 0], [⟨.hyperplane, 2⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![1, 0], [⟨.unit, 0⟩, ⟨.exceptional 0, 3⟩]⟩,
      ⟨2, ![1, 0], [⟨.exceptional 0, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![1, 0], [⟨.unit, 1⟩, ⟨.exceptional 0, 2⟩]⟩,
      ⟨2, ![1, 0], [⟨.exceptional 0, 2⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![1, 0], [⟨.unit, 0⟩, ⟨.point, 2⟩]⟩,
      ⟨2, ![1, 0], [⟨.point, 2⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![1, 0], [⟨.unit, 1⟩, ⟨.point, 1⟩]⟩,
      ⟨2, ![1, 0], [⟨.point, 1⟩, ⟨.unit, 1⟩]⟩]]

/-- Ordinary specializations in the same frame. -/
def values : Fin 4 → Fin 4 → ℚ :=
  ![![(13 / 2880), (13 / 2880), (13 / 960), (13 / 960)],
    ![0, 0, 0, 0],
    ![(-1 / 240), (-1 / 240), (-1 / 80), (-1 / 80)],
    ![0, 0, 0, 0]]

end OneBlowup

namespace TwoBlowups

/-- Ordered requests in string-first, string-last, dilaton-first, dilaton-last order. -/
def requests : Fin 10 → Fin 4 → SurfaceQuery .blowupTwo :=
  ![![⟨2, ![1, 0, 0], [⟨.unit, 0⟩, ⟨.unit, 4⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.unit, 4⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.unit, 1⟩, ⟨.unit, 3⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.unit, 3⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![1, 0, 0], [⟨.unit, 0⟩, ⟨.hyperplane, 3⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.hyperplane, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.unit, 1⟩, ⟨.hyperplane, 2⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.hyperplane, 2⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![1, 0, 0], [⟨.unit, 0⟩, ⟨.exceptional 0, 3⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.exceptional 0, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.unit, 1⟩, ⟨.exceptional 0, 2⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.exceptional 0, 2⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![1, 0, 0], [⟨.unit, 0⟩, ⟨.exceptional 1, 3⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.exceptional 1, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.unit, 1⟩, ⟨.exceptional 1, 2⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.exceptional 1, 2⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![1, 0, 0], [⟨.unit, 0⟩, ⟨.point, 2⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.point, 2⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.unit, 1⟩, ⟨.point, 1⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.point, 1⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![0, 1, 0], [⟨.unit, 0⟩, ⟨.unit, 4⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.unit, 4⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.unit, 1⟩, ⟨.unit, 3⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.unit, 3⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![0, 1, 0], [⟨.unit, 0⟩, ⟨.hyperplane, 3⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.hyperplane, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.unit, 1⟩, ⟨.hyperplane, 2⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.hyperplane, 2⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![0, 1, 0], [⟨.unit, 0⟩, ⟨.exceptional 0, 3⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.exceptional 0, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.unit, 1⟩, ⟨.exceptional 0, 2⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.exceptional 0, 2⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![0, 1, 0], [⟨.unit, 0⟩, ⟨.exceptional 1, 3⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.exceptional 1, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.unit, 1⟩, ⟨.exceptional 1, 2⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.exceptional 1, 2⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![0, 1, 0], [⟨.unit, 0⟩, ⟨.point, 2⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.point, 2⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.unit, 1⟩, ⟨.point, 1⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.point, 1⟩, ⟨.unit, 1⟩]⟩]]

/-- Ordinary specializations in the same frame. -/
def values : Fin 10 → Fin 4 → ℚ :=
  ![![(13 / 2880), (13 / 2880), (13 / 960), (13 / 960)],
    ![0, 0, 0, 0],
    ![(-1 / 240), (-1 / 240), (-1 / 80), (-1 / 80)],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![(13 / 2880), (13 / 2880), (13 / 960), (13 / 960)],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![(-1 / 240), (-1 / 240), (-1 / 80), (-1 / 80)],
    ![0, 0, 0, 0]]

end TwoBlowups

namespace StrictLine

/-- Ordered requests in string-first, string-last, dilaton-first, dilaton-last order. -/
def requests : Fin 4 → Fin 4 → SurfaceQuery .blowupTwo :=
  ![![⟨2, ![0, 0, 1], [⟨.unit, 0⟩, ⟨.unit, 4⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.unit, 4⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.unit, 1⟩, ⟨.unit, 3⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.unit, 3⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![0, 0, 1], [⟨.unit, 0⟩, ⟨.hyperplane, 3⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.hyperplane, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.unit, 1⟩, ⟨.hyperplane, 2⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.hyperplane, 2⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![0, 0, 1], [⟨.unit, 0⟩, ⟨.exceptional 0, 3⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.exceptional 0, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.unit, 1⟩, ⟨.exceptional 0, 2⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.exceptional 0, 2⟩, ⟨.unit, 1⟩]⟩],
    ![⟨2, ![0, 0, 1], [⟨.unit, 0⟩, ⟨.exceptional 1, 3⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.exceptional 1, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.unit, 1⟩, ⟨.exceptional 1, 2⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.exceptional 1, 2⟩, ⟨.unit, 1⟩]⟩]]

/-- Ordinary specializations in the same frame. -/
def values : Fin 4 → Fin 4 → ℚ :=
  ![![(13 / 2880), (13 / 2880), (13 / 960), (13 / 960)],
    ![(1 / 240), (1 / 240), (1 / 80), (1 / 80)],
    ![(1 / 240), (1 / 240), (1 / 80), (1 / 80)],
    ![(1 / 240), (1 / 240), (1 / 80), (1 / 80)]]

end StrictLine

namespace StrictLinePoint

/-- Ordered requests in string-first, string-last, dilaton-first, dilaton-last order. -/
def requests : Fin 1 → Fin 4 → SurfaceQuery .blowupTwo :=
  ![![⟨2, ![0, 0, 1], [⟨.unit, 0⟩, ⟨.point, 2⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.point, 2⟩, ⟨.unit, 0⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.unit, 1⟩, ⟨.point, 1⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.point, 1⟩, ⟨.unit, 1⟩]⟩]]

/-- Ordinary specializations in the same frame. -/
def values : Fin 1 → Fin 4 → ℚ :=
  ![![0, 0, 0, 0]]

end StrictLinePoint

end AxiomaticGW.GKM.GenusTwoUnitPairs
