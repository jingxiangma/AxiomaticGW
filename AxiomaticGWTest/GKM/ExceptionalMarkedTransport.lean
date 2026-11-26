/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalOrdinaryTransport

/-! # Multiple insertions on a double exceptional cover -/

public section
namespace AxiomaticGWTest.GKM.ExceptionalMarkedTransport
open AxiomaticGW AxiomaticGW.GKM
open GKM.ExceptionalMarkedTransport ExceptionalMarkedGraphSupport ExceptionalCharacterField
open EquivariantCoefficients (Coefficient x)
open CurveReplay.OneBlowup renaming tables → f1
open SurfaceFrames.TwoBlowups renaming request → twoFrame

/-- Two hyperplanes followed by the selected exceptional divisor, with distinct cotangent powers. -/
@[expose] def marks (i : Fin 2) : List (SurfaceInsertion .blowupTwo) :=
  [⟨.hyperplane, 0⟩, ⟨.hyperplane, 3⟩, ⟨.exceptional i, 2⟩]

/-- On the double cover the hyperplanes lie at opposite ends, the divisor at the target. -/
@[expose] def doubleCover : MarkedAt f1 (2 • SurfaceTarget.hirzebruchOne.exceptionalCurve 0) 3 :=
  ⟨⟨2, 1, FixedGraphSupport.singleCover f1 2 2 false,
    by rw [FixedGraphSupport.degree_singleCover]; decide +kernel⟩, ![0, 1, 1]⟩

/-- The E₁ shift appears twice, whereas the same marked product vanishes on E₂. -/
theorem two_hyperplanes (i : Fin 2) :
    insertionFactor (T := CurveReplay.TwoBlowups.tables) (targetQuery i 2 2 (marks i))
      twoFrame.restrictions
      (markedEquiv i 2 3 doubleCover) = if i = 0 then x ^ 3 else 0 := by
  apply (product_transport i 2 2 (marks i) doubleCover).trans
  have value : sourceProduct i 2 (marks i) doubleCover = if i = 0 then x ^ 3 else 0 := by
    unfold sourceProduct
    change (∏ j : Fin 3, _) = _
    rw [Fin.prod_univ_three]
    fin_cases i
    · change (0 + x * 1) * (0 + x * 1) * x = x ^ 3
      ring
    · change (0 + 0 * 1) * (0 + 0 * 1) * x = (0 : Coefficient)
      ring
  rw [value]
  fin_cases i
  · rfl
  · exact map_zero _

/-- A pair of opposite weight poles on the marked double cover has a regular total.
The first weighted product itself has a simple pole. -/
theorem cancel_after_summing (q : ℚ) :
    let f := insertionFactor (T := CurveReplay.TwoBlowups.tables) (targetQuery 0 2 2 (marks 0))
      twoFrame.restrictions (markedEquiv 0 2 3 doubleCover)
    EquivariantCoefficients.Specializes (f / x^4 + f * (1 - 1/x^4)) 0 ∧
      ¬EquivariantCoefficients.Specializes (f / x^4) q := by
  dsimp only
  rw [two_hyperplanes, if_pos rfl]
  have hs : x^3 / x^4 + x^3 * (1-1/x^4) = x^3 := by ring
  have hp : x^3 / x^4 = x⁻¹ := by field_simp [EquivariantCoefficients.x_ne_zero]
  rw [hs, hp]
  have hx : EquivariantCoefficients.Specializes x 0 := by
    simpa only [EquivariantCoefficients.atZero, MvPolynomial.eval₂Hom_X', Pi.zero_apply] using
      EquivariantCoefficients.specializes_of_eq_polynomial (MvPolynomial.X 0) (f := x) rfl
  refine ⟨?_, EquivariantCoefficients.not_specializes_inverse (MvPolynomial.X 0)
    EquivariantCoefficients.x_ne_zero (by
      simp only [EquivariantCoefficients.atZero, MvPolynomial.eval₂Hom_X', Pi.zero_apply]) q⟩
  simpa only [zero_pow (by decide : 3 ≠ 0)] using hx.pow 3

end AxiomaticGWTest.GKM.ExceptionalMarkedTransport
