/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoF1PositivePairs
public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.TwoBlowup

/-! # Full ordinary comparison for two positive cotangent powers at energy one

The four ordered request grids contain 57 entries, including the 26 with
a second unit descendant. Both marking orders retain their original mixed
calibration expansions. The two second unit descendants give 19/960 in
each primitive class. Pairing one with a first divisor descendant gives
−5/288 on its own exceptional curve, 5/288 for H, E₁ or E₂ on the strict
line, and zero for the other exceptional-class requests.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoPositivePairs
open SurfaceGenusTwoBlowupDescendants

private theorem compare_row {X : SurfaceTarget} (i : Fin X.blowups)
    {source incoming : SurfaceQuery X} {a b : ℚ} (h : queryValue? i source = some a)
    (he : incoming = source ∧ b = a) : queryValue? i incoming = some b := by
  rw [he.1, he.2, h]

namespace ExceptionalOne

/-- Ordinary GKM specialization agrees with the full ordered reconstruction throughout the grid. -/
theorem all_accepted (j k : Fin 4) :
    queryValue? 0 (requests j k) = some (values j k) := by
  cases j using Fin.cases with
  | zero =>
    fin_cases k
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 0) (by decide +kernel)
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 1) (by decide +kernel)
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 2) (by decide +kernel)
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 3) (by decide +kernel)
  | succ j =>
    cases k using Fin.cases with
    | zero =>
      fin_cases j
      · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 4) (by decide +kernel)
      · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 5) (by decide +kernel)
      · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 6) (by decide +kernel)
    | succ k => exact divisors_accepted j k

end ExceptionalOne

namespace ExceptionalTwo

/-- Ordinary GKM specialization agrees with the full ordered reconstruction throughout the grid. -/
theorem all_accepted (j k : Fin 4) :
    queryValue? 0 (requests j k) = some (values j k) := by
  cases j using Fin.cases with
  | zero =>
    fin_cases k
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 7) (by decide +kernel)
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 8) (by decide +kernel)
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 9) (by decide +kernel)
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 10) (by decide +kernel)
  | succ j =>
    cases k using Fin.cases with
    | zero =>
      fin_cases j
      · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 11) (by decide +kernel)
      · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 12) (by decide +kernel)
      · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 13) (by decide +kernel)
    | succ k => exact divisors_accepted j k

end ExceptionalTwo

namespace StrictLine

/-- Ordinary GKM specialization agrees with the full ordered reconstruction throughout the grid. -/
theorem all_accepted (j k : Fin 4) :
    queryValue? 0 (requests j k) = some (values j k) := by
  cases j using Fin.cases with
  | zero =>
    fin_cases k
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 14) (by decide +kernel)
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 15) (by decide +kernel)
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 16) (by decide +kernel)
    · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 17) (by decide +kernel)
  | succ j =>
    cases k using Fin.cases with
    | zero =>
      fin_cases j
      · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 18) (by decide +kernel)
      · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 19) (by decide +kernel)
      · exact compare_row 0 (GenusTwoSecondUnitPairs.TwoBlowup.accepted 20) (by decide +kernel)
    | succ k => exact divisors_accepted j k

end StrictLine

end AxiomaticGW.GKM.GenusTwoPositivePairs
