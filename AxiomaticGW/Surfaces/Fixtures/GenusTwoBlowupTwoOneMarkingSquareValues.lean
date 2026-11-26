/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoOneMarkingSquare
import AxiomaticGW.Surfaces.GenusTwoL24PointCache
import AxiomaticGW.Surfaces.Fixtures.GenusOneBl2Table

/-! # High-psi one-marked ancestors at the two exceptional curves of the two-point blowup -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoExceptionalOneMarking
open SurfaceGenusTwo

set_option Elab.async false
set_option maxRecDepth 65536

private abbrev X := SurfaceTarget.blowupTwo
private abbrev beta0 : X.Curve := ![1, 0, 0]
private abbrev beta1 : X.Curve := ![0, 1, 0]

private def rational (beta : X.Curve) : ℚ :=
  if X.effective.energy beta ≤ 12 then GenusZeroBl2Table.values beta
  else SurfaceGenusZero.pointValue X beta

private def elliptic (beta : X.Curve) : ℚ :=
  if X.effective.energy beta ≤ 12 then GenusOneBl2Table.values beta
  else SurfaceGenusOne.pointValue X beta

private theorem rational_eq : rational = SurfaceGenusZero.pointValue X := by
  funext beta
  unfold rational
  split_ifs with h
  · exact SurfaceGenusZero.checkBoundedValues_sound X 12 _ GenusZeroBl2Table.accepted beta h
  · rfl

private theorem elliptic_eq : elliptic = SurfaceGenusOne.pointValue X := by
  funext beta
  unfold elliptic
  split_ifs with h
  · exact SurfaceGenusOne.checkBoundedValues_sound X 12 _ _ GenusOneBl2Table.accepted beta h
  · rfl

open GenusTwoPsiSquare

private def graph (beta : X.Curve) (a : SurfaceBasisLabel X) (k : ℕ) (i : Fin 10) : ℚ :=
  (boundaryTerm i).1.surfaceDecoratedEval X (constantVertexWithPoints X rational elliptic)
    (boundaryTerm i).2 beta (fun _ ↦ k) (fun _ ↦ a)

private def unitRows : Fin 10 → ℚ :=
  ![1/576, 1/576, 0, 1/576, 1/6, 1/8, 0, 1/24, 1/24, 2]

private def divisorRows : Fin 10 → ℚ :=
  ![-1/288, -1/288, -1/576, 0, -1/12, -1/12, 0, 0, -1/24, -1]

private theorem square_eq (beta : X.Curve) (a : SurfaceBasisLabel X) (k : ℕ)
    (rows : Fin 10 → ℚ) (h : ∀ i, graph beta a k i = rows i) :
    oneMarkingSquareValue beta a k = ∑ i, boundary (boundaryIndex i) * rows i := by
  unfold oneMarkingSquareValue
  rw [← constantVertexWithPoints_eq X rational elliptic rational_eq elliptic_eq]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg (boundary (boundaryIndex i) * ·) (h i)

-- Checking individual graphs keeps each closed kernel reduction small.
set_option maxHeartbeats 1600000 in
-- The surviving external psi power adds a lower-genus recursion to these ten graphs.
private theorem unit_0 : oneMarkingSquareValue beta0 .unit 1 = 1/240 := by
  refine (square_eq _ _ _ unitRows ?_).trans (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

private theorem hyperplane_0 : oneMarkingSquareValue beta0 .hyperplane 0 = 0 := by
  refine (square_eq _ _ _ 0 ?_).trans (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

private theorem first_0 : oneMarkingSquareValue beta0 (.exceptional 0) 0 = -13/2880 := by
  refine (square_eq _ _ _ divisorRows ?_).trans (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

private theorem second_0 : oneMarkingSquareValue beta0 (.exceptional 1) 0 = 0 := by
  refine (square_eq _ _ _ 0 ?_).trans (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 1600000 in
-- The surviving external psi power adds a lower-genus recursion to these ten graphs.
private theorem unit_1 : oneMarkingSquareValue beta1 .unit 1 = 1/240 := by
  refine (square_eq _ _ _ unitRows ?_).trans (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

private theorem hyperplane_1 : oneMarkingSquareValue beta1 .hyperplane 0 = 0 := by
  refine (square_eq _ _ _ 0 ?_).trans (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

private theorem first_1 : oneMarkingSquareValue beta1 (.exceptional 0) 0 = 0 := by
  refine (square_eq _ _ _ 0 ?_).trans (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

private theorem second_1 : oneMarkingSquareValue beta1 (.exceptional 1) 0 = -13/2880 := by
  refine (square_eq _ _ _ divisorRows ?_).trans (by decide +kernel)
  intro i
  fin_cases i <;> decide +kernel

private theorem exceptional_coordinates (i : Fin 2) :
    SurfaceTarget.blowupTwo.exceptionalCurve i = (![beta0, beta1] : Fin 2 → _) i := by
  fin_cases i <;> decide +kernel

/-- Each exceptional class has unit ancestor 1/240 and vanishing hyperplane ancestor.
The exceptional divisor ancestor distinguishes its own curve from the other generator. -/
theorem exceptional_ancestors (base : SurfaceAncestorKey .blowupTwo → ℚ) (i : Fin 2) :
    let beta := SurfaceTarget.blowupTwo.exceptionalCurve i
    ancestorValue base (oneMarkingKey beta .unit 3) = 1/240 ∧
    ancestorValue base (oneMarkingKey beta .hyperplane 2) = 0 ∧
    ∀ j : Fin 2, ancestorValue base (oneMarkingKey beta (.exceptional j) 2) =
      if i = j then -13/2880 else 0 := by
  dsimp only
  rw [exceptional_coordinates]
  refine ⟨(ancestorValue_oneMarking_square base _ .unit 1).trans ?_,
    (ancestorValue_oneMarking_square base _ .hyperplane 0).trans ?_, ?_⟩
  · fin_cases i
    · exact unit_0
    · exact unit_1
  · fin_cases i
    · exact hyperplane_0
    · exact hyperplane_1
  · intro j
    refine (ancestorValue_oneMarking_square base _ (.exceptional j) 0).trans ?_
    fin_cases i <;> fin_cases j
    · exact first_0
    · exact second_0
    · exact first_1
    · exact second_1

end AxiomaticGW.BlowupTwoExceptionalOneMarking
