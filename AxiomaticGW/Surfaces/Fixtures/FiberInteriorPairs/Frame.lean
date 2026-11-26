/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPairTerms
public import AxiomaticGW.Surfaces.GenusTwoPulledSquare
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPositiveSquareComponents

/-! # Ancestor keys for the interior two-marked requests on an F₁ fiber

The original square relation distinguishes the selected and extra markings.
The product relation distinguishes its two positive occurrences. Each frame
is checked against the ordering chosen by the original ancestor evaluator.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs

abbrev X := SurfaceTarget.hirzebruchOne
abbrev boundary (s : SurfaceGenusTwoBlowupOrder.State X) :=
  SurfaceGenusTwoBlowupBoundary.value s.1 s.2
abbrev low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundary

def squareBeta : Fin 19 → X.Curve :=
  ![![0, 0],
    ![0, 0],
    ![0, 0],
    ![0, 0],
    ![0, 0],
    ![0, 0],
    ![0, 1],
    ![0, 1],
    ![0, 1],
    ![0, 1],
    ![0, 1],
    ![0, 1],
    ![0, 1],
    ![0, 1],
    ![0, 1],
    ![0, 1],
    ![0, 1],
    ![0, 1],
    ![0, 1]]

def oldMark : Fin 19 → SurfaceInsertion X :=
  ![⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩]

def extraMark : Fin 19 → SurfaceInsertion X :=
  ![⟨.unit, 0⟩,
    ⟨.unit, 0⟩,
    ⟨.unit, 0⟩,
    ⟨.hyperplane, 0⟩,
    ⟨.exceptional 0, 0⟩,
    ⟨.unit, 1⟩,
    ⟨.point, 0⟩,
    ⟨.point, 0⟩,
    ⟨.point, 0⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.point, 1⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.unit, 3⟩]

def squareKey (j : Fin 19) : SurfaceAncestorKey X :=
  pairKey (squareBeta j) (oldMark j) (extraMark j)

def powers (j : Fin 19) : Option (Fin 1) → ℕ :=
  fun x ↦ Option.elim x (extraMark j).psi (fun _ ↦ (oldMark j).psi - 2)

def labels (j : Fin 19) : Option (Fin 1) → SurfaceBasisLabel X :=
  fun x ↦ Option.elim x (extraMark j).label (fun _ ↦ (oldMark j).label)

theorem square_framed (j : Fin 19) : ancestorValue low (squareKey j) =
    pulledSquare (vertex (ancestorValue low)) 1 (squareBeta j) (powers j) (labels j) := by
  fin_cases j
  all_goals
    rw [ancestorValue_pulledSquare low _ rfl (by decide +kernel) (by decide +kernel), ← vertex_eq]
    congr 1 <;> decide +kernel

def productBeta : Fin 4 → X.Curve :=
  ![![0, 0],
    ![0, 0],
    ![0, 1],
    ![0, 1]]

def productLabels : Fin 4 → Fin 2 → SurfaceBasisLabel X :=
  ![![.unit, .hyperplane],
    ![.unit, .exceptional 0],
    ![.hyperplane, .point],
    ![.exceptional 0, .point]]

def productKey (j : Fin 4) : SurfaceAncestorKey X :=
  pairKey (productBeta j) ⟨productLabels j 0, 1⟩ ⟨productLabels j 1, 1⟩

theorem product_framed (j : Fin 4) : ancestorValue low (productKey j) =
    ∑ i, productGraph (vertex low) (productBeta j) (productLabels j) i := by
  rw [vertex_eq]
  fin_cases j
  all_goals
    exact ancestorValue_twoMarking_product low _ rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ (by decide +kernel) (by decide +kernel)

def lowKey : Fin 9 → SurfaceAncestorKey X :=
  ![pairKey (X := X) ![0, 0] ⟨.unit, 0⟩ ⟨.point, 1⟩,
    pairKey (X := X) ![0, 0] ⟨.hyperplane, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) ![0, 0] ⟨.hyperplane, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) ![0, 0] ⟨.hyperplane, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) ![0, 0] ⟨.exceptional 0, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) ![0, 0] ⟨.exceptional 0, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) ![0, 0] ⟨.exceptional 0, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) ![0, 0] ⟨.point, 0⟩ ⟨.unit, 1⟩,
    pairKey (X := X) ![0, 1] ⟨.point, 0⟩ ⟨.point, 1⟩]

end AxiomaticGW.BlowupF1FiberInteriorPairs
