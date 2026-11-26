/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.IncidenceFrame

/-! # Termwise vanishing on the exceptional-face squares

Each retained full-class square and each primitive tail has zero on every signed source.
The same incidence argument works for both the primitive foreign-label and mixed-curve cases.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveSquare

theorem full_support (j : Fin 16) (i : Fin 11) :
    FaceSquares.check (squareBeta (Fin.natAdd 12 j)) (oldMark (Fin.natAdd 12 j))
      (extraMark (Fin.natAdd 12 j)) i = true :=
  FaceSquares.checked _ i

/-- All 308 signed sources of the twenty-eight original square ancestors vanish. -/
theorem square_parts (c : CertifiedComponents X) (j : Fin 28) (i : Fin 11) :
    squarePart c j i = 0 := FaceSquares.part_of_check c j i (FaceSquares.checked j i)

theorem primitive_parts (c : CertifiedComponents X) (j : Fin 12) (i : Fin 11) :
    squarePart c (Fin.castAdd 16 j) i = 0 := square_parts c _ i

theorem full_parts (c : CertifiedComponents X) (j : Fin 16) (i : Fin 11) :
    squarePart c (Fin.natAdd 12 j) i = 0 := square_parts c _ i

theorem square_values (j : Fin 28) : ancestorValue low (squareKey j) = 0 := by
  rw [square_sum (CertifiedComponents.bounded X)]
  simp only [square_parts, Finset.sum_const_zero]

/-- The corresponding E₁ source with an E₁ marking survives the same support test. -/
theorem primitive_supported : FaceSquares.check ![1,0,0] ⟨.unit, 2⟩ ⟨.exceptional 0, 1⟩ 1 =
    false := by decide +kernel

set_option maxHeartbeats 4000000 in
-- This source sums every marking and splitting in the primitive exceptional class.
/-- The supported primitive source has its nonzero value on the original component evaluator. -/
theorem primitive_source :
    pulledSquarePart (component (ancestorValue low)) 1 (![1, 0, 0] : X.Curve)
      (Option.elim · 1 (fun _ ↦ 0)) (Option.elim · (.exceptional 0) (fun _ ↦ .unit)) 1 =
      -155 / 33696 := by
  rw [← (CertifiedComponents.bounded X).vertex_eq]
  decide +kernel

end AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
