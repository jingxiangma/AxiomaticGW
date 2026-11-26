module

public import AxiomaticGW.Surfaces.Queries

/-!
# Native two-marked positive-cotangent claims in anticanonical degree one

Report SHA256: 565e0ee2ad547d80becd6e854f6776c4b3e36a75454047504d9b464cc07bfba1
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoPositivePairs

namespace OneBlowup

/-- Ordered localization requests. -/
def requests : Fin 3 → Fin 3 → SurfaceQuery .hirzebruchOne :=
  ![![⟨2, ![1, 0], [⟨.unit, 2⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![1, 0], [⟨.unit, 2⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![1, 0], [⟨.unit, 2⟩, ⟨.exceptional 0, 1⟩]⟩],
    ![⟨2, ![1, 0], [⟨.hyperplane, 1⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![1, 0], [⟨.hyperplane, 1⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![1, 0], [⟨.hyperplane, 1⟩, ⟨.exceptional 0, 1⟩]⟩],
    ![⟨2, ![1, 0], [⟨.exceptional 0, 1⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![1, 0], [⟨.exceptional 0, 1⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![1, 0], [⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 1⟩]⟩]]

/-- Ordinary specialization in the same basis and marking order. -/
def values : Fin 3 → Fin 3 → ℚ :=
  ![![(19 / 960), 0, (-5 / 288)],
    ![0, 0, 0],
    ![(-5 / 288), 0, (1 / 144)]]

end OneBlowup

namespace ExceptionalOne

/-- Ordered localization requests. -/
def requests : Fin 4 → Fin 4 → SurfaceQuery .blowupTwo :=
  ![![⟨2, ![1, 0, 0], [⟨.unit, 2⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.unit, 2⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.unit, 2⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.unit, 2⟩, ⟨.exceptional 1, 1⟩]⟩],
    ![⟨2, ![1, 0, 0], [⟨.hyperplane, 1⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.hyperplane, 1⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.hyperplane, 1⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.hyperplane, 1⟩, ⟨.exceptional 1, 1⟩]⟩],
    ![⟨2, ![1, 0, 0], [⟨.exceptional 0, 1⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.exceptional 0, 1⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.exceptional 0, 1⟩, ⟨.exceptional 1, 1⟩]⟩],
    ![⟨2, ![1, 0, 0], [⟨.exceptional 1, 1⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.exceptional 1, 1⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.exceptional 1, 1⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![1, 0, 0], [⟨.exceptional 1, 1⟩, ⟨.exceptional 1, 1⟩]⟩]]

/-- Ordinary specialization in the same basis and marking order. -/
def values : Fin 4 → Fin 4 → ℚ :=
  ![![(19 / 960), 0, (-5 / 288), 0],
    ![0, 0, 0, 0],
    ![(-5 / 288), 0, (1 / 144), 0],
    ![0, 0, 0, 0]]

end ExceptionalOne

namespace ExceptionalTwo

/-- Ordered localization requests. -/
def requests : Fin 4 → Fin 4 → SurfaceQuery .blowupTwo :=
  ![![⟨2, ![0, 1, 0], [⟨.unit, 2⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.unit, 2⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.unit, 2⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.unit, 2⟩, ⟨.exceptional 1, 1⟩]⟩],
    ![⟨2, ![0, 1, 0], [⟨.hyperplane, 1⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.hyperplane, 1⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.hyperplane, 1⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.hyperplane, 1⟩, ⟨.exceptional 1, 1⟩]⟩],
    ![⟨2, ![0, 1, 0], [⟨.exceptional 0, 1⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.exceptional 0, 1⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.exceptional 0, 1⟩, ⟨.exceptional 1, 1⟩]⟩],
    ![⟨2, ![0, 1, 0], [⟨.exceptional 1, 1⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.exceptional 1, 1⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.exceptional 1, 1⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![0, 1, 0], [⟨.exceptional 1, 1⟩, ⟨.exceptional 1, 1⟩]⟩]]

/-- Ordinary specialization in the same basis and marking order. -/
def values : Fin 4 → Fin 4 → ℚ :=
  ![![(19 / 960), 0, 0, (-5 / 288)],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![(-5 / 288), 0, 0, (1 / 144)]]

end ExceptionalTwo

namespace StrictLine

/-- Ordered localization requests. -/
def requests : Fin 4 → Fin 4 → SurfaceQuery .blowupTwo :=
  ![![⟨2, ![0, 0, 1], [⟨.unit, 2⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.unit, 2⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.unit, 2⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.unit, 2⟩, ⟨.exceptional 1, 1⟩]⟩],
    ![⟨2, ![0, 0, 1], [⟨.hyperplane, 1⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.hyperplane, 1⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.hyperplane, 1⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.hyperplane, 1⟩, ⟨.exceptional 1, 1⟩]⟩],
    ![⟨2, ![0, 0, 1], [⟨.exceptional 0, 1⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.exceptional 0, 1⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.exceptional 0, 1⟩, ⟨.exceptional 1, 1⟩]⟩],
    ![⟨2, ![0, 0, 1], [⟨.exceptional 1, 1⟩, ⟨.unit, 2⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.exceptional 1, 1⟩, ⟨.hyperplane, 1⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.exceptional 1, 1⟩, ⟨.exceptional 0, 1⟩]⟩,
      ⟨2, ![0, 0, 1], [⟨.exceptional 1, 1⟩, ⟨.exceptional 1, 1⟩]⟩]]

/-- Ordinary specialization in the same basis and marking order. -/
def values : Fin 4 → Fin 4 → ℚ :=
  ![![(19 / 960), (5 / 288), (5 / 288), (5 / 288)],
    ![(5 / 288), (1 / 144), (1 / 144), (1 / 144)],
    ![(5 / 288), (1 / 144), (1 / 144), (1 / 144)],
    ![(5 / 288), (1 / 144), (1 / 144), (1 / 144)]]

end StrictLine

end AxiomaticGW.GKM.GenusTwoPositivePairs
