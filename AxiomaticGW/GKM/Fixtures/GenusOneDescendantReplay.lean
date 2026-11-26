/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusOneDescendants

/-!
# Native genus-one descendant replay at multiple arities

Input SHA256: a491511628b617a08126dad54d214e37a9b562b8bb1842022f41f7565d16edb9
Actual incoming claims are checked against the proved all-arity evaluator.
The digest records provenance; geometric applicability remains conditional.
-/

@[expose] public section

namespace AxiomaticGW.GKM.GenusOneDescendantReplay

namespace Plane

/-- Actual incoming full requests in source order. -/
def requests : Fin 14 → SurfaceQuery .plane :=
  ![⟨1, ![0], [⟨.unit, 1⟩]⟩,
    ⟨1, ![0], [⟨.unit, 2⟩, ⟨.unit, 0⟩]⟩,
    ⟨1, ![0], [⟨.unit, 1⟩, ⟨.unit, 1⟩]⟩,
    ⟨1, ![0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩]⟩,
    ⟨1, ![0], [⟨.unit, 1⟩, ⟨.hyperplane, 0⟩]⟩,
    ⟨1, ![0], [⟨.hyperplane, 0⟩, ⟨.unit, 1⟩]⟩,
    ⟨1, ![0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩]⟩,
    ⟨1, ![1], [⟨.point, 2⟩]⟩,
    ⟨1, ![1], [⟨.hyperplane, 3⟩]⟩,
    ⟨1, ![1], [⟨.unit, 4⟩]⟩,
    ⟨1, ![1], [⟨.point, 3⟩, ⟨.unit, 0⟩]⟩,
    ⟨1, ![1], [⟨.hyperplane, 3⟩, ⟨.hyperplane, 0⟩]⟩,
    ⟨1, ![1], []⟩,
    ⟨1, ![2], [⟨.point, 5⟩]⟩]

/-- Actual incoming ordinary values, without recomputation by the exporter. -/
def values : Fin 14 → ℚ :=
  ![(1 / 8),
    (1 / 8),
    (1 / 8),
    (1 / 4),
    (-1 / 8),
    (-1 / 8),
    (3 / 4),
    0,
    (1 / 8),
    (-1 / 4),
    0,
    (1 / 8),
    0,
    (1 / 32)]

/-- Full request coverage is fixed separately from incoming values. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceGenusOneDescendants.requests .plane).toFinset := by decide +kernel

/-- Genus, full class, arity, insertion powers and labels are claim-bound. -/
theorem accepted : ∀ i, SurfaceGenusOne.queryValue? (requests i) =
    some (values i) := by decide +kernel

end Plane

namespace OneBlowup

/-- Actual incoming full requests in source order. -/
def requests : Fin 12 → SurfaceQuery .hirzebruchOne :=
  ![⟨1, ![0, 0], [⟨.unit, 1⟩]⟩,
    ⟨1, ![0, 0], [⟨.unit, 2⟩, ⟨.unit, 0⟩]⟩,
    ⟨1, ![0, 0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩]⟩,
    ⟨1, ![0, 0], [⟨.unit, 1⟩, ⟨.exceptional 0, 0⟩]⟩,
    ⟨1, ![0, 0], [⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩]⟩,
    ⟨1, ![1, 0], [⟨.exceptional 0, 1⟩]⟩,
    ⟨1, ![1, 0], [⟨.unit, 2⟩]⟩,
    ⟨1, ![1, 0], [⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 0⟩]⟩,
    ⟨1, ![1, 0], []⟩,
    ⟨1, ![2, 0], [⟨.exceptional 0, 2⟩]⟩,
    ⟨1, ![0, 1], [⟨.point, 1⟩]⟩,
    ⟨1, ![1, 1], [⟨.hyperplane, 3⟩]⟩]

/-- Actual incoming ordinary values, without recomputation by the exporter. -/
def values : Fin 12 → ℚ :=
  ![(1 / 6),
    (1 / 6),
    (1 / 3),
    (-1 / 24),
    (-1 / 24),
    (1 / 12),
    (1 / 24),
    (-1 / 12),
    0,
    (-1 / 16),
    (-1 / 12),
    (1 / 8)]

/-- Full request coverage is fixed separately from incoming values. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceGenusOneDescendants.requests .hirzebruchOne).toFinset := by decide +kernel

/-- Genus, full class, arity, insertion powers and labels are claim-bound. -/
theorem accepted : ∀ i, SurfaceGenusOne.queryValue? (requests i) =
    some (values i) := by decide +kernel

end OneBlowup

namespace TwoBlowups

/-- Actual incoming full requests in source order. -/
def requests : Fin 15 → SurfaceQuery .blowupTwo :=
  ![⟨1, ![0, 0, 0], [⟨.unit, 1⟩]⟩,
    ⟨1, ![0, 0, 0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩]⟩,
    ⟨1, ![0, 0, 0], [⟨.unit, 1⟩, ⟨.exceptional 1, 0⟩]⟩,
    ⟨1, ![1, 0, 0], [⟨.exceptional 0, 1⟩]⟩,
    ⟨1, ![0, 1, 0], [⟨.exceptional 0, 1⟩]⟩,
    ⟨1, ![0, 1, 0], [⟨.exceptional 1, 1⟩]⟩,
    ⟨1, ![1, 0, 0], [⟨.unit, 2⟩]⟩,
    ⟨1, ![0, 1, 0], [⟨.exceptional 1, 1⟩, ⟨.exceptional 1, 0⟩]⟩,
    ⟨1, ![0, 0, 1], [⟨.hyperplane, 1⟩]⟩,
    ⟨1, ![0, 0, 1], [⟨.exceptional 0, 1⟩]⟩,
    ⟨1, ![0, 0, 1], []⟩,
    ⟨1, ![1, 0, 0], []⟩,
    ⟨1, ![2, 0, 0], [⟨.exceptional 0, 2⟩]⟩,
    ⟨1, ![1, 0, 1], [⟨.point, 1⟩]⟩,
    ⟨1, ![1, 1, 1], [⟨.hyperplane, 3⟩]⟩]

/-- Actual incoming ordinary values, without recomputation by the exporter. -/
def values : Fin 15 → ℚ :=
  ![(5 / 24),
    (5 / 12),
    (-1 / 24),
    (1 / 12),
    0,
    (1 / 12),
    (1 / 24),
    (-1 / 12),
    (-1 / 12),
    (-1 / 12),
    0,
    0,
    (-1 / 16),
    (-1 / 12),
    (1 / 8)]

/-- Full request coverage is fixed separately from incoming values. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceGenusOneDescendants.requests .blowupTwo).toFinset := by decide +kernel

/-- Genus, full class, arity, insertion powers and labels are claim-bound. -/
theorem accepted : ∀ i, SurfaceGenusOne.queryValue? (requests i) =
    some (values i) := by decide +kernel

end TwoBlowups

end AxiomaticGW.GKM.GenusOneDescendantReplay
