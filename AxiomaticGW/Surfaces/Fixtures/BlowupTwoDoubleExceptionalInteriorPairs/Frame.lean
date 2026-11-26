/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalSingletons
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.Transfer
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.SquareSources

/-! # Original two-marked ancestor frame on the double exceptional curves of Bl₂

Each axis uses the same two coordinates for its own and foreign exceptional divisor.
The effective class and all absolute surface labels are retained in every public key.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare
open BlowupTwoDoubleExceptionalDivisor (beta)

/-- The two-point blowup on which both exceptional axes are evaluated. -/
abbrev X := SurfaceTarget.blowupTwo
/-- The certified canonical table on the exceptional face. -/
abbrev boundary := BlowupTwoExceptionalPlaneZeroTable.table
/-- The original low-cotangent genus-two evaluator with this table. -/
abbrev low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundary

/-- The five constant and twelve primitive ancestor keys from the original calibration. -/
def tailCurve (i : Fin 2) (j : Fin 17) : X.Curve := if j.val < 5 then 0 else X.exceptionalCurve i

/-- The first insertion in each lower-class ancestor multiset. -/
def tailFirst (i : Fin 2) (j : Fin 17) : SurfaceInsertion X :=
  (#[⟨.exceptional i, 0⟩, ⟨.exceptional i, 0⟩, ⟨.exceptional i, 0⟩, ⟨.exceptional i, 0⟩,
    ⟨.exceptional i, 0⟩, ⟨.exceptional i, 0⟩, ⟨.exceptional i, 0⟩, ⟨.exceptional i, 0⟩,
    ⟨.exceptional i, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
    ⟨.point, 0⟩, ⟨.hyperplane, 1⟩, ⟨.exceptional i, 1⟩, ⟨.exceptional i, 1⟩,
    ⟨.exceptional i, 1⟩] : Array (SurfaceInsertion X))[j.val]'j.isLt

/-- The companion insertion in each lower-class ancestor multiset. -/
def tailSecond (i : Fin 2) (j : Fin 17) : SurfaceInsertion X :=
  (#[⟨.point, 0⟩, ⟨.hyperplane, 1⟩, ⟨.exceptional i, 1⟩, ⟨.exceptional i.rev, 1⟩,
    ⟨.unit, 2⟩, ⟨.hyperplane, 2⟩, ⟨.exceptional i, 2⟩, ⟨.exceptional i.rev, 2⟩,
    ⟨.unit, 3⟩, ⟨.hyperplane, 1⟩, ⟨.exceptional i, 1⟩, ⟨.exceptional i.rev, 1⟩,
    ⟨.unit, 2⟩, ⟨.exceptional i, 1⟩, ⟨.exceptional i, 1⟩, ⟨.exceptional i.rev, 1⟩,
    ⟨.unit, 2⟩] : Array (SurfaceInsertion X))[j.val]'j.isLt

/-- The complete two-marked key of a constant or primitive calibration term. -/
def tailKey (i : Fin 2) (j : Fin 17) : SurfaceAncestorKey X :=
  pairKey (tailCurve i j) (tailFirst i j) (tailSecond i j)

/-- The marking selected by the original cotangent square on its full-class key. -/
def oldMark (i : Fin 2) (j : Fin 16) : SurfaceInsertion X :=
  (#[⟨.hyperplane, 2⟩, ⟨.exceptional i, 2⟩, ⟨.exceptional i.rev, 2⟩, ⟨.unit, 3⟩,
    ⟨.hyperplane, 2⟩, ⟨.exceptional i, 2⟩, ⟨.exceptional i.rev, 2⟩, ⟨.unit, 3⟩,
    ⟨.hyperplane, 2⟩, ⟨.exceptional i, 2⟩, ⟨.exceptional i.rev, 2⟩, ⟨.unit, 3⟩,
    ⟨.unit, 2⟩, ⟨.unit, 2⟩, ⟨.unit, 2⟩, ⟨.unit, 2⟩] : Array (SurfaceInsertion X))[j.val]'j.isLt

/-- The additional marking carried along the pulled-back cotangent equation. -/
def extraMark (i : Fin 2) (j : Fin 16) : SurfaceInsertion X :=
  (#[⟨.hyperplane, 1⟩, ⟨.hyperplane, 1⟩, ⟨.hyperplane, 1⟩, ⟨.hyperplane, 1⟩,
    ⟨.exceptional i, 1⟩, ⟨.exceptional i, 1⟩, ⟨.exceptional i, 1⟩, ⟨.exceptional i, 1⟩,
    ⟨.exceptional i.rev, 1⟩, ⟨.exceptional i.rev, 1⟩,
    ⟨.exceptional i.rev, 1⟩, ⟨.exceptional i.rev, 1⟩,
    ⟨.hyperplane, 2⟩, ⟨.exceptional i, 2⟩, ⟨.exceptional i.rev, 2⟩, ⟨.unit, 3⟩] :
    Array (SurfaceInsertion X))[j.val]'j.isLt

/-- The sixteen full-class squares in the order fixed by the selected cotangent occurrence. -/
def squareKey (i : Fin 2) (j : Fin 16) : SurfaceAncestorKey X :=
  pairKey (beta i) (oldMark i j) (extraMark i j)

/-- General two-marked cotangent powers on the pullback of the original one-marked square. -/
def powers (i : Fin 2) (j : Fin 16) : Option (Fin 1) → ℕ :=
  fun t ↦ Option.elim t (extraMark i j).psi (fun _ ↦ (oldMark i j).psi - 2)

/-- Absolute basis labels in the selected and additional slots. -/
def labels (i : Fin 2) (j : Fin 16) : Option (Fin 1) → SurfaceBasisLabel X :=
  fun t ↦ Option.elim t (extraMark i j).label (fun _ ↦ (oldMark i j).label)

/-- One of the eleven signed graphs, retaining every assignment of curve and node labels. -/
def squarePart (c : CertifiedComponents X) (i : Fin 2) (j : Fin 16) (g : Fin 11) : ℚ :=
  pulledSquarePart (c.vertex (ancestorValue low)) 1 (beta i) (powers i j) (labels i j) g

theorem square_sum (c : CertifiedComponents X) (i : Fin 2) (j : Fin 16) :
    ancestorValue low (squareKey i j) = ∑ g, squarePart c i j g := by
  have h : ancestorValue low (squareKey i j) =
      pulledSquare (vertex (ancestorValue low)) 1 (beta i) (powers i j) (labels i j) := by
    fin_cases i <;> fin_cases j
    all_goals
      rw [ancestorValue_pulledSquare low _ rfl (by decide +kernel) (by decide +kernel), ← vertex_eq]
      congr 1 <;> decide +kernel
  rw [h, pulledSquare_eq_parts, ← component_eq, ← c.vertex_eq]
  rfl

end AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
