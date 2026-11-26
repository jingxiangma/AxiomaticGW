/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPairTerms
public import AxiomaticGW.Surfaces.GenusTwoPulledSquare
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPositiveSquareComponents

/-! # Ancestor keys for the interior two-marked requests in the class 2E on F₁

The original square relation distinguishes the selected and extra markings.
The product relation distinguishes its two positive occurrences. Each frame
is checked against the ordering chosen by the original ancestor evaluator.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs

abbrev X := SurfaceTarget.hirzebruchOne
abbrev boundary (s : SurfaceGenusTwoBlowupOrder.State X) :=
  SurfaceGenusTwoBlowupBoundary.value s.1 s.2
abbrev low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundary

def squareBeta : Fin 15 → X.Curve :=
  ![![0, 0],
    ![1, 0],
    ![1, 0],
    ![1, 0],
    ![1, 0],
    ![1, 0],
    ![2, 0],
    ![2, 0],
    ![2, 0],
    ![2, 0],
    ![2, 0],
    ![2, 0],
    ![2, 0],
    ![2, 0],
    ![2, 0]]

def oldMark : Fin 15 → SurfaceInsertion X :=
  ![⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩]

def extraMark : Fin 15 → SurfaceInsertion X :=
  ![⟨.exceptional 0, 0⟩,
    ⟨.exceptional 0, 0⟩,
    ⟨.exceptional 0, 0⟩,
    ⟨.exceptional 0, 0⟩,
    ⟨.point, 0⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.unit, 3⟩]

def squareKey (j : Fin 15) : SurfaceAncestorKey X :=
  pairKey (squareBeta j) (oldMark j) (extraMark j)

def powers (j : Fin 15) : Option (Fin 1) → ℕ :=
  fun x ↦ Option.elim x (extraMark j).psi (fun _ ↦ (oldMark j).psi - 2)

def labels (j : Fin 15) : Option (Fin 1) → SurfaceBasisLabel X :=
  fun x ↦ Option.elim x (extraMark j).label (fun _ ↦ (oldMark j).label)

theorem square_framed (j : Fin 15) : ancestorValue low (squareKey j) =
    pulledSquare (vertex (ancestorValue low)) 1 (squareBeta j) (powers j) (labels j) := by
  fin_cases j
  all_goals
    rw [ancestorValue_pulledSquare low _ rfl (by decide +kernel) (by decide +kernel), ← vertex_eq]
    congr 1 <;> decide +kernel

abbrev exceptional : X.Curve := ![1, 0]

def productLabels : Fin 2 → Fin 2 → SurfaceBasisLabel X :=
  ![![.hyperplane, .exceptional 0],
    ![.exceptional 0, .exceptional 0]]

def productKey (j : Fin 2) : SurfaceAncestorKey X :=
  pairKey exceptional ⟨productLabels j 0, 1⟩ ⟨productLabels j 1, 1⟩

def lowKey : Fin 5 → SurfaceAncestorKey X :=
  ![pairKey (X := X) ![0, 0] ⟨.exceptional 0, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) ![0, 0] ⟨.exceptional 0, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) ![0, 0] ⟨.exceptional 0, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) ![1, 0] ⟨.point, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) ![1, 0] ⟨.point, 0⟩ ⟨.exceptional 0, 1⟩]

end AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs
