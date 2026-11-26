/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoDegreeZeroDescendants

/-!
# Genus-two degree-zero descendant replay on all three targets

Input SHA256: d96ab1d950e42af002f3c1b0ec999881bd204d7faa5d6f07486675bc06732c2c
The full incoming ordinary claims are checked against the reconstructed values.
Geometric interpretation uses the named inputs of the soundness theorem.
This does not certify localization or import CohFT classes.
-/

@[expose] public section

set_option Elab.async false

namespace AxiomaticGW.GKM.GenusTwoDegreeZeroReplay

namespace Plane

/-- Complete incoming requests, preserving the target and full class. -/
def requests : Fin 1 → SurfaceQuery .plane :=
  ![⟨2, ![0], [⟨.unit, 2⟩]⟩]

/-- Exact ordinary values supplied by the pinned producer. -/
def values : Fin 1 → ℚ :=
  ![(7 / 640)]

/-- Every supplied answer belongs to the complete requested descendant. -/
theorem accepted : ∀ i,
    SurfaceGenusTwo.degreeZeroOnePointQueryValue? (requests i) =
      some (values i) := by
  decide +kernel

end Plane

namespace OneBlowup

/-- Complete incoming requests, preserving the target and full class. -/
def requests : Fin 1 → SurfaceQuery .hirzebruchOne :=
  ![⟨2, ![0, 0], [⟨.unit, 2⟩]⟩]

/-- Exact ordinary values supplied by the pinned producer. -/
def values : Fin 1 → ℚ :=
  ![(7 / 720)]

/-- Every supplied answer belongs to the complete requested descendant. -/
theorem accepted : ∀ i,
    SurfaceGenusTwo.degreeZeroOnePointQueryValue? (requests i) =
      some (values i) := by
  decide +kernel

end OneBlowup

namespace TwoBlowups

/-- Complete incoming requests, preserving the target and full class. -/
def requests : Fin 1 → SurfaceQuery .blowupTwo :=
  ![⟨2, ![0, 0, 0], [⟨.unit, 2⟩]⟩]

/-- Exact ordinary values supplied by the pinned producer. -/
def values : Fin 1 → ℚ :=
  ![(49 / 5760)]

/-- Every supplied answer belongs to the complete requested descendant. -/
theorem accepted : ∀ i,
    SurfaceGenusTwo.degreeZeroOnePointQueryValue? (requests i) =
      some (values i) := by
  decide +kernel

end TwoBlowups

end AxiomaticGW.GKM.GenusTwoDegreeZeroReplay
