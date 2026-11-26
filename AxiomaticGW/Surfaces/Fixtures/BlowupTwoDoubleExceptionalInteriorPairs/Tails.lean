/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.Fourth
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPrimitiveDivisorProduct
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.IncidenceSquares

/-! # Constant and primitive ancestors of the doubled exceptional interior pairs

On each exceptional axis, seven terms use the low-cotangent rule, three use the
primitive divisor product and seven use the pulled square with its eleven signed sources.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants SurfaceGenusTwoPositiveSquare
open SurfaceGenusTwoPositiveDivisorPairs

/-- The two absolute exceptional axes give the same values in the own/foreign label order. -/
def tailValues (_ : Fin 2) : Fin 17 → ℚ :=
  ![0, 0, 0, 0, -1/2880, 0, 1/240, 0, -5/576, 0, 0, 0, 0, 0, 1/144, 0, -17/960]

private def lowIndex : Fin 7 → Fin 17 := ![0, 1, 2, 3, 9, 10, 11]

private theorem terminal_values (i : Fin 2) (k : Fin 7) :
    ancestorValue low (tailKey i (lowIndex k)) = tailValues i (lowIndex k) := by
  fin_cases i <;> fin_cases k <;>
    rw [ancestorValue_low low _ rfl (by decide +kernel)] <;> decide +kernel

private def productIndex : Fin 3 → Fin 17 := ![13, 14, 15]

private theorem product_values (i : Fin 2) (k : Fin 3) :
    ancestorValue low (tailKey i (productIndex k)) = tailValues i (productIndex k) := by
  let j := productIndex k
  let beta := X.exceptionalCurve i
  let a := (tailFirst i j).label
  let b := (tailSecond i j).label
  have he : X.effective.energy beta = 1 := by fin_cases i <;> decide +kernel
  have ha : a.codimension = 1 := by fin_cases i <;> fin_cases k <;> decide +kernel
  have hb : b.codimension = 1 := by fin_cases i <;> fin_cases k <;> decide +kernel
  have h := Option.some.inj ((queryValue?_firstDivisorPair 0 beta he a b ha hb).symm.trans
    (queryValue?_primitiveDivisorProduct 0 beta he a b ha hb))
  have hp : SurfaceGenusTwoBlowupRecursion.values 0 (beta, .point) = 0 := by
    rw [← BlowupTwoExceptionalPlaneZeroTable.table_eq]
    fin_cases i <;> decide +kernel
  rw [hp, mul_zero, add_zero] at h
  have hkey : tailKey i j = pairKey beta ⟨a, 1⟩ ⟨b, 1⟩ := by
    fin_cases i <;> fin_cases k <;> decide +kernel
  change ancestorValueWith boundary (tailKey i j) = _
  rw [hkey, ancestorValueWith_eq_of_table 0 2 boundary
    (fun s _ ↦ BlowupTwoExceptionalPlaneZeroTable.table_eq s) _ rfl (by
      change X.effective.energy beta ≤ 2
      omega)]
  refine h.trans ?_
  fin_cases i <;> fin_cases k <;> decide +kernel

private def high : Fin 7 → Fin 17 := ![4, 5, 6, 7, 8, 12, 16]

private def tailPowers (i : Fin 2) (j : Fin 7) : Option (Fin 1) → ℕ :=
  fun k ↦ Option.elim k (tailFirst i (high j)).psi (fun _ ↦ (tailSecond i (high j)).psi - 2)

private def tailLabels (i : Fin 2) (j : Fin 7) : Option (Fin 1) → SurfaceBasisLabel X :=
  fun k ↦ Option.elim k (tailFirst i (high j)).label (fun _ ↦ (tailSecond i (high j)).label)

private def part (i : Fin 2) (j : Fin 7) (g : Fin 11) : ℚ :=
  pulledSquarePart
    ((Fourth.backend i).vertex (ancestorValue low))
    1 (tailCurve i (high j)) (tailPowers i j) (tailLabels i j) g

private theorem sum_parts (i : Fin 2) (j : Fin 7) :
    ancestorValue low (tailKey i (high j)) = ∑ g, part i j g := by
  have h : ancestorValue low (tailKey i (high j)) =
      pulledSquare (vertex (ancestorValue low)) 1 (tailCurve i (high j))
        (tailPowers i j) (tailLabels i j) := by
    fin_cases i <;> fin_cases j
    all_goals
      rw [ancestorValue_pulledSquare low _ rfl (by decide +kernel) (by decide +kernel), ← vertex_eq]
      congr 1 <;> decide +kernel
  rw [h, pulledSquare_eq_parts, ← component_eq,
    ← (Fourth.backend i).vertex_eq]
  rfl

private def partValues : Fin 7 → Fin 11 → ℚ :=
  ![![-1/2880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    0,
    ![-1/2880, 155/101088, 35/50544, 23/224640, 0, 7/33696, 31/16848, 0, 0, 1/8320, 1/56160],
    0,
    ![0, -155/67392, -35/33696, -23/224640, 41/143208, -7/11232, -155/33696, 0,
      -101/11456640, -1/4160, -1/18720],
    0,
    ![0, -155/33696, -35/16848, -23/44928, 0, -7/16848, -31/5616, -749/168480, 0,
      -1/8320, -1/56160]]

private theorem of_incidence (i : Fin 2) (j : Fin 7) (g : Fin 11)
    (h : BlowupTwoMixedExceptionalInteriorPairs.FaceSquares.check (tailCurve i (high j))
      (tailSecond i (high j)) (tailFirst i (high j)) g = true) : part i j g = 0 :=
  pulledSquarePart_eq_zero_of_support _ _
    (BlowupTwoMixedExceptionalInteriorPairs.FaceSquares.vertexZero_sound
      (Fourth.backend i) (ancestorValue low))
    _ _ _ _ g h

private def vanishingSquare : Fin 3 → Fin 7 := ![1, 3, 5]

private def survivingSquare : Fin 4 → Fin 7 := ![0, 2, 4, 6]

set_option maxRecDepth 65536 in
private theorem zero_parts (i : Fin 2) (k : Fin 3) (g : Fin 11) :
    part i (vanishingSquare k) g = 0 := by
  apply of_incidence
  fin_cases i <;> fin_cases k <;> fin_cases g <;> decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
-- Surviving incidence assignments use the original lower-genus boundary equations.
private theorem surviving_parts (i : Fin 2) (k : Fin 4) (g : Fin 11) :
    part i (survivingSquare k) g = partValues (survivingSquare k) g := by
  fin_cases i <;> fin_cases k <;> fin_cases g <;> decide +kernel

private theorem square_cases : ∀ j : Fin 7,
    (∃ k, vanishingSquare k = j) ∨ ∃ k, survivingSquare k = j := by decide +kernel

private theorem vanishing_value : ∀ (k : Fin 3) (g : Fin 11),
    partValues (vanishingSquare k) g = 0 := by decide +kernel

private theorem signed_parts (i : Fin 2) (j : Fin 7) (g : Fin 11) :
    part i j g = partValues j g := by
  rcases square_cases j with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact (zero_parts i k g).trans (vanishing_value k g).symm
  · exact surviving_parts i k g

private theorem sum_values : ∀ (i : Fin 2) (j : Fin 7),
    ∑ g, partValues j g = tailValues i (high j) := by decide +kernel

private theorem high_values (i : Fin 2) (j : Fin 7) :
    ancestorValue low (tailKey i (high j)) = tailValues i (high j) :=
  (sum_parts i j).trans
    ((Finset.sum_congr rfl (fun g _ ↦ signed_parts i j g)).trans (sum_values i j))

/-- Evaluation of every constant or primitive ancestor in the original doubled-axis transfer. -/
theorem tail_values (i : Fin 2) (j : Fin 17) :
    ancestorValue low (tailKey i j) = tailValues i j := by
  have h : (∃ k, lowIndex k = j) ∨ (∃ k, productIndex k = j) ∨ ∃ k, high k = j := by
    revert j
    decide +kernel
  rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact terminal_values i k
  · exact product_values i k
  · exact high_values i k

end AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
