/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.BPSources

/-! # Original unshifted BP row values at the two rulings

The hyperplane and foreign exceptional rows have a lower-genus constant
of 1/120, cancelled by the three actual class-zero divisor seeds.
The own exceptional row forces its canonical first descendant to vanish.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.BP
open SurfaceGenusTwoBlowupScalar BelorousskiPandharipande
open _root_.AxiomaticGW.BlowupTwoLineBP (canonicalFamily)

/-- Relative row order HHH, own exceptional cube, and foreign exceptional cube. -/
def chartRow (i : Fin 2) : Fin 3 → Fin 3 := ![0, i.succ, i.rev.succ]

/-- The complete same-ruling coefficients in absolute H, P, N, K₁, K₂ order. -/
def fullCoefficients (i : Fin 2) (r : Fin 3) : Fin 5 → ℚ :=
  if r = 0 then ![18, -18, 0, 0, 0]
  else if r = 1 then (if i = 0 then ![0, 0, 0, -18, 0] else ![0, 0, 0, 0, -18])
  else if i = 0 then ![0, 18, 0, 0, -18] else ![0, 18, 0, -18, 0]

/-- Only class-zero columns with nonzero initial values enter the reduced equation. -/
def seedIndex : Fin 3 → Fin 5 := ![0, 3, 4]

/-- H₀, K₁,₀, K₂,₀ coefficients of each original row. -/
def seedCoefficients (i : Fin 2) (r : Fin 3) : Fin 3 → ℚ :=
  if r = 1 then 0 else if i = 0 then ![12, 0, -12] else ![12, -12, 0]

/-- Only the first of the sixteen remaining lower-genus diagrams can contribute. -/
def constantValue (r : Fin 3) : ℚ := if r = 1 then 0 else 1/120

set_option maxRecDepth 65536
set_option Elab.async false

set_option maxHeartbeats 2000000 in
-- Each full lower-genus source has the one additional marked point.
/-- Constant of every original unshifted BP equation. -/
theorem constant_value (i : Fin 2) (r : Fin 3) :
    constant 0 (curve i, row (chartRow i r)) = constantValue r := by
  rw [constant_eq]
  fin_cases i <;> fin_cases r <;> decide +kernel

/-- The marked genus-two coefficient graph with its exact paper weight and multiplicity. -/
def signed (i : Fin 2) (r : Fin 3) (full : Bool) (j : Fin 5) (k : Fin 4) : ℚ :=
  rawPaperCoefficient (Fin.castAdd 16 k) * (6 * diagram i (chartRow i r) full j k)

set_option maxHeartbeats 3000000 in
-- Each zero-class first descendant appears in the original second paper diagram.
/-- Signed class-zero contributions before adding the four BP diagrams. -/
theorem seed_signed (i : Fin 2) (r j : Fin 3) (k : Fin 4) :
    signed i r false (seedIndex j) k = if k = 1 then seedCoefficients i r j else 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases j <;> fin_cases k <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- The same-class point column comes from the fourth diagram and the other columns from the third.
/-- The four full-class signed coefficients include the original primary N column. -/
theorem full_signed (i : Fin 2) (r : Fin 3) (j : Fin 5) (k : Fin 4) :
    signed i r true j k =
      if k = (if j = 1 then 3 else 2) then fullCoefficients i r j else 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases j <;> fin_cases k <;> decide +kernel

/-- Complete original same-class coefficients with the absolute exceptional labels. -/
theorem full_coefficient (i : Fin 2) (r : Fin 3) (j : Fin 5) :
    singletonCoefficient 0 (curve i, row (chartRow i r)) (variableAt i true j) =
      fullCoefficients i r j := by
  rw [coefficient_eq]
  change ∑ k, signed i r true j k = _
  simp only [full_signed, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Complete coefficients of the nonzero class-zero seeds. -/
theorem seed_coefficient (i : Fin 2) (r j : Fin 3) :
    singletonCoefficient 0 (curve i, row (chartRow i r)) (variableAt i false (seedIndex j)) =
      seedCoefficients i r j := by
  rw [coefficient_eq]
  change ∑ k, signed i r false (seedIndex j) k = _
  simp only [seed_signed, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end AxiomaticGW.BlowupTwoRuling.BP
