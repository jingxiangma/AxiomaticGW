/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GW.Descendants.Exceptional
import AxiomaticGW.Frobenius.Examples

/-!
# Numerical boundary regressions

These finite fixtures check the exceptional string and dilaton equations with
nonzero normalized values. They do not construct a geometric GW theory or an
all-genus point model. In particular the positive-degree fixture below tests
signed coefficients, without asserting geometric values for a curve class.
-/

set_option linter.privateModule false

namespace AxiomaticGWTest.Exceptional

open AxiomaticGW

private def pointPairing : SymmetricPerfectPairing ℚ ℚ :=
  (CommFrobeniusAlgebra.baseRing ℚ).pairing

/-- The two normalized point boundary profiles, with unit insertions. Values
outside these profiles are fixture values, not a proposed intersection theory. -/
private noncomputable def pointBoundaryValue (g : ℕ) (S : Type)
    [Fintype S] (k : S → ℕ) : ℚ := by
  classical
  exact if g = 0 ∧ Fintype.card S = 3 ∧ (∀ s, k s = 0) then 1
    else if g = 1 ∧ Fintype.card S = 1 ∧ (∀ s, k s = 1) then 1 / 24
    else 0

/-- Genus-zero primary string transitions from zero, one, and two remaining
marks. The last transition has normalized value one, with zero lowering sum. -/
example (n : Fin 3) :
    pointBoundaryValue 0 (Option (Fin n.val)) (fun _ ↦ 0) =
      (∑ s : Fin n.val, if (0 : ℕ) = 0 then 0 else
        pointBoundaryValue 0 (Fin n.val) (lowerPower (fun _ ↦ 0) s)) +
      stringCorrection pointPairing 0 (Fin n.val) (0 : ℕ)
        (fun _ ↦ 0) (fun _ ↦ 1) := by
  fin_cases n
  · norm_num [pointBoundaryValue, stringCorrection, twoPointPairing]
  · norm_num [pointBoundaryValue, stringCorrection, twoPointPairing]
  · rw [stringCorrection_zero_fin_two]
    norm_num [pointBoundaryValue, pointPairing,
      CommFrobeniusAlgebra.baseRing_pairing_apply]

/-- Adding a dilaton insertion gives zero at all three genus-zero,
degree-zero unstable-base transitions. -/
example (n : Fin 3) :
    pointBoundaryValue 0 (Option (Fin n.val))
        (fun | none => 1 | some _ => 0) =
      dilatonCoefficient ℚ 0 (Fin n.val) *
          pointBoundaryValue 0 (Fin n.val) (fun _ ↦ 0) +
        dilatonCorrection (1 / 24 : ℚ) 0 (Fin n.val) (0 : ℕ) := by
  fin_cases n <;>
    norm_num [pointBoundaryValue, dilatonCoefficient, dilatonCorrection]
  exact ⟨none, by decide⟩

/-- The genus-one empty-base string transition vanishes. -/
example :
    pointBoundaryValue 1 (Option Empty) (fun _ ↦ 0) =
      (∑ s : Empty, if (0 : ℕ) = 0 then 0 else
        pointBoundaryValue 1 Empty (lowerPower (fun _ ↦ 0) s)) +
      stringCorrection pointPairing 1 Empty (0 : ℕ)
        (fun _ ↦ 0) (fun s ↦ nomatch s) := by
  norm_num [pointBoundaryValue, stringCorrection]

/-- The missing genus-one dilaton correction must preserve the positive
point value `1/24`, even though the coefficient of the empty invariant is zero. -/
example :
    pointBoundaryValue 1 (Option Empty) (fun _ ↦ 1) =
      dilatonCoefficient ℚ 1 Empty *
          pointBoundaryValue 1 Empty (fun _ ↦ 0) +
        dilatonCorrection (1 / 24 : ℚ) 1 Empty (0 : ℕ) := by
  norm_num [pointBoundaryValue, dilatonCoefficient, dilatonCorrection]

/-- A nonzero numerical fixture for successive positive-degree dilaton
insertions at base arities zero, one, and two. -/
private def positiveDegreeDilatonValues : Fin 4 → ℚ := ![1, -2, 2, 0]

example (n : Fin 3) :
    positiveDegreeDilatonValues n.succ =
      dilatonCoefficient ℚ 0 (Fin n.val) *
          positiveDegreeDilatonValues n.castSucc +
        dilatonCorrection (1 / 24 : ℚ) 0 (Fin n.val) (1 : ℕ) := by
  fin_cases n <;>
    norm_num [positiveDegreeDilatonValues, dilatonCoefficient, dilatonCorrection,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- A positive cotangent power removes the genus-zero metric exception. -/
example :
    pointBoundaryValue 0 (Option (Fin 2))
        (fun | none => 0 | some i => ![1, 0] i) =
      (∑ s : Fin 2, if ![1, 0] s = 0 then 0 else
        pointBoundaryValue 0 (Fin 2) (lowerPower ![1, 0] s)) +
      stringCorrection pointPairing 0 (Fin 2) (0 : ℕ)
        ![1, 0] (fun _ ↦ 1) := by
  norm_num [pointBoundaryValue, stringCorrection, Fin.sum_univ_two]
  exact ⟨some 0, by decide⟩

/-- Relabelling two different scalar inputs preserves their metric value. -/
example :
    twoPointPairing pointPairing (Fin 2) ![2, 3] = 6 ∧
      twoPointPairing pointPairing (Fin 2)
        (fun i ↦ ![2, 3] (Equiv.swap 0 1 i)) = 6 := by
  norm_num [twoPointPairing_fin_two, pointPairing,
    CommFrobeniusAlgebra.baseRing_pairing_apply]

/-- Positive degree removes both exceptions, even at their exceptional
genus and marking counts. -/
example :
    stringCorrection pointPairing 0 (Fin 2) (1 : ℕ)
        (fun _ ↦ 0) (fun _ ↦ 1) = 0 ∧
      dilatonCorrection (1 / 24 : ℚ) 1 Empty (1 : ℕ) = 0 := by
  norm_num [stringCorrection, dilatonCorrection]

/-- Changing the genus or adding a remaining marking removes the
genus-one correction. The genus condition also removes the metric exception. -/
example :
    dilatonCorrection (1 / 24 : ℚ) 0 Empty (0 : ℕ) = 0 ∧
      dilatonCorrection (1 / 24 : ℚ) 1 (Fin 1) (0 : ℕ) = 0 ∧
      stringCorrection pointPairing 1 (Fin 2) (0 : ℕ)
        (fun _ ↦ 0) (fun _ ↦ 1) = 0 := by
  norm_num [stringCorrection, dilatonCorrection]

/-- The three planned surface Euler-characteristic scalars stay distinct.
This checks parameter dependence; geometric identification belongs to R1. -/
example :
    dilatonCorrection (3 / 24 : ℚ) 1 Empty (0 : ℕ) = 1 / 8 ∧
      dilatonCorrection (4 / 24 : ℚ) 1 Empty (0 : ℕ) = 1 / 6 ∧
      dilatonCorrection (5 / 24 : ℚ) 1 Empty (0 : ℕ) = 5 / 24 := by
  norm_num [dilatonCorrection]

end AxiomaticGWTest.Exceptional
