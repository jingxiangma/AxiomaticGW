/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.CertifiedComponentLayers
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.Frame

/-! # Evaluation of an original exceptional-face square with checked vertices -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare

/-- One signed source, retaining its complete marking and effective splitting sums. -/
def squarePart (c : CertifiedComponents X) (j : Fin 28) (i : Fin 11) : ℚ :=
  pulledSquarePart (c.vertex (ancestorValue low)) 1 (squareBeta j) (powers j) (labels j) i

theorem square_sum (c : CertifiedComponents X) (j : Fin 28) :
    ancestorValue low (squareKey j) = ∑ i, squarePart c j i := by
  rw [square_framed, pulledSquare_eq_parts, ← component_eq, ← c.vertex_eq]
  rfl

end AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
