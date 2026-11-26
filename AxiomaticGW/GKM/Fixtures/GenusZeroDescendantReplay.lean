/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusZeroDescendants

/-!
# Native genus-zero descendant replay at multiple arities

Input SHA256: 1123c7b21c528d78363ae1cf3ffb1c05e55864c649405bc186dd8f251b30fd39
Actual incoming claims are checked against the proved all-arity evaluator.
The digest records provenance; geometric applicability remains conditional.
-/

@[expose] public section

namespace AxiomaticGW.GKM.GenusZeroDescendantReplay

namespace Plane

def requests : Fin 12 → SurfaceQuery .plane :=
  ![⟨0, ![0], [⟨.unit, 1⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩]⟩,
    ⟨0, ![0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩]⟩,
    ⟨0, ![0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩]⟩,
    ⟨0, ![0], [⟨.unit, 2⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩]⟩,
    ⟨0, ![1], [⟨.point, 3⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩]⟩,
    ⟨0, ![1], [⟨.hyperplane, 4⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
    ⟨0, ![1], [⟨.point, 1⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩]⟩,
    ⟨0, ![1], [⟨.point, 4⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩]⟩,
    ⟨0, ![1], [⟨.point, 1⟩]⟩,
    ⟨0, ![1], [⟨.hyperplane, 2⟩]⟩,
    ⟨0, ![1], [⟨.point, 2⟩, ⟨.unit, 0⟩]⟩,
    ⟨0, ![1], [⟨.hyperplane, 2⟩, ⟨.hyperplane, 0⟩]⟩]

def values : Fin 12 → ℚ :=
  ![1, 2, 6, 1, 1, -2, 1, 1, 1, -3, 1, -2]

/-- Full request coverage is fixed separately from incoming values. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceGenusZeroDescendants.requests .plane).toFinset := by decide +kernel

/-- Genus, full class, arity, insertion powers and labels are claim-bound. -/
theorem accepted : ∀ i, SurfaceGenusZero.queryValue? (requests i) =
    some (values i) := by decide +kernel

end Plane

namespace OneBlowup

def requests : Fin 10 → SurfaceQuery .hirzebruchOne :=
  ![⟨0, ![0, 0], [⟨.unit, 1⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 0⟩]⟩,
    ⟨0, ![0, 0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 0⟩]⟩,
    ⟨0, ![1, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
    ⟨0, ![2, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 1⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
    ⟨0, ![1, 0], []⟩,
    ⟨0, ![1, 0], [⟨.exceptional 0, 0⟩]⟩,
    ⟨0, ![1, 0], [⟨.unit, 1⟩]⟩,
    ⟨0, ![1, 0], [⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩]⟩,
    ⟨0, ![0, 1], [⟨.point, 0⟩]⟩,
    ⟨0, ![1, 1], [⟨.point, 3⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩]⟩]

def values : Fin 10 → ℚ :=
  ![-1, -2, 1, (-3 / 2), 1, -1, -2, 1, 1, 1]

/-- Full request coverage is fixed separately from incoming values. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceGenusZeroDescendants.requests .hirzebruchOne).toFinset := by decide +kernel

/-- Genus, full class, arity, insertion powers and labels are claim-bound. -/
theorem accepted : ∀ i, SurfaceGenusZero.queryValue? (requests i) =
    some (values i) := by decide +kernel

end OneBlowup

namespace TwoBlowups

def requests : Fin 12 → SurfaceQuery .blowupTwo :=
  ![⟨0, ![0, 0, 0], [⟨.unit, 1⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 0⟩]⟩,
    ⟨0, ![0, 0, 0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 0⟩]⟩,
    ⟨0, ![1, 0, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
    ⟨0, ![0, 1, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
    ⟨0, ![0, 1, 0], [⟨.exceptional 1, 2⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
    ⟨0, ![0, 0, 1], [⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 1⟩]⟩,
    ⟨0, ![0, 0, 1], []⟩,
    ⟨0, ![1, 0, 0], []⟩,
    ⟨0, ![0, 1, 0], []⟩,
    ⟨0, ![1, 0, 0], [⟨.unit, 1⟩]⟩,
    ⟨0, ![0, 1, 1], [⟨.point, 0⟩]⟩,
    ⟨0, ![1, 0, 1], [⟨.point, 0⟩]⟩]

def values : Fin 12 → ℚ :=
  ![0, -2, 1, 0, 1, 1, 1, 1, 1, -2, 1, 1]

/-- Full request coverage is fixed separately from incoming values. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceGenusZeroDescendants.requests .blowupTwo).toFinset := by decide +kernel

/-- Genus, full class, arity, insertion powers and labels are claim-bound. -/
theorem accepted : ∀ i, SurfaceGenusZero.queryValue? (requests i) =
    some (values i) := by decide +kernel

end TwoBlowups

end AxiomaticGW.GKM.GenusZeroDescendantReplay
