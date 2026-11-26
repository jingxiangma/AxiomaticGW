/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoExceptionalPlaneZeroTable
public import AxiomaticGW.Surfaces.GenusTwoPairTerms
public import AxiomaticGW.Surfaces.GenusTwoPulledSquare
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPositiveSquareComponents

/-! # Ancestor keys for the interior two-marked requests in class E₁ + E₂ on Bl₂

The original square relation distinguishes the selected and extra markings.
The product relation distinguishes its two positive occurrences. Each frame
is checked against the ordering chosen by the original ancestor evaluator.
The two marking arrays are indexed directly inside repeated graph contractions.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs

abbrev X := SurfaceTarget.blowupTwo
abbrev boundary := BlowupTwoExceptionalPlaneZeroTable.table
abbrev low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundary

/-- The two primitive tails precede the sixteen squares on the full class. -/
def squareBeta (j : Fin 28) : X.Curve :=
  if j.val < 6 then ![0, 1, 0] else if j.val < 12 then ![1, 0, 0] else ![1, 1, 0]

def oldMark (j : Fin 28) : SurfaceInsertion X :=
  (#[⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩] :
    Array (SurfaceInsertion X))[j.val]'j.isLt

def extraMark (j : Fin 28) : SurfaceInsertion X :=
  (#[⟨.exceptional 0, 0⟩,
    ⟨.exceptional 0, 0⟩,
    ⟨.exceptional 0, 0⟩,
    ⟨.exceptional 0, 0⟩,
    ⟨.point, 0⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 0⟩,
    ⟨.exceptional 1, 0⟩,
    ⟨.exceptional 1, 0⟩,
    ⟨.exceptional 1, 0⟩,
    ⟨.point, 0⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.unit, 3⟩] :
    Array (SurfaceInsertion X))[j.val]'j.isLt

def squareKey (j : Fin 28) : SurfaceAncestorKey X :=
  pairKey (squareBeta j) (oldMark j) (extraMark j)

def powers (j : Fin 28) : Option (Fin 1) → ℕ :=
  fun x ↦ Option.elim x (extraMark j).psi (fun _ ↦ (oldMark j).psi - 2)

def labels (j : Fin 28) : Option (Fin 1) → SurfaceBasisLabel X :=
  fun x ↦ Option.elim x (extraMark j).label (fun _ ↦ (oldMark j).label)

theorem square_framed (j : Fin 28) : ancestorValue low (squareKey j) =
    pulledSquare (vertex (ancestorValue low)) 1 (squareBeta j) (powers j) (labels j) := by
  fin_cases j
  all_goals
    rw [ancestorValue_pulledSquare low _ rfl (by decide +kernel) (by decide +kernel), ← vertex_eq]
    congr 1 <;> decide +kernel

def productBeta (j : Fin 6) : X.Curve := if j.val < 3 then ![0, 1, 0] else ![1, 0, 0]

def productLabels : Fin 6 → Fin 2 → SurfaceBasisLabel X :=
  ![![.hyperplane, .exceptional 0],
    ![.exceptional 0, .exceptional 0],
    ![.exceptional 0, .exceptional 1],
    ![.hyperplane, .exceptional 1],
    ![.exceptional 0, .exceptional 1],
    ![.exceptional 1, .exceptional 1]]

def productKey (j : Fin 6) : SurfaceAncestorKey X :=
  pairKey (productBeta j) ⟨productLabels j 0, 1⟩ ⟨productLabels j 1, 1⟩

def lowKey : Fin 10 → SurfaceAncestorKey X :=
  ![pairKey (X := X) ![0, 0, 0] ⟨.exceptional 0, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) ![0, 0, 0] ⟨.exceptional 0, 0⟩ ⟨.exceptional 1, 1⟩,
    pairKey (X := X) ![0, 0, 0] ⟨.exceptional 1, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) ![0, 0, 0] ⟨.exceptional 1, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) ![0, 1, 0] ⟨.point, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) ![0, 1, 0] ⟨.point, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) ![0, 1, 0] ⟨.point, 0⟩ ⟨.exceptional 1, 1⟩,
    pairKey (X := X) ![1, 0, 0] ⟨.point, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) ![1, 0, 0] ⟨.point, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) ![1, 0, 0] ⟨.point, 0⟩ ⟨.exceptional 1, 1⟩]

end AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
