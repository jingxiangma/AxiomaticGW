/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.WDVV

/-!
# Checked genus-zero equations for the blowup base cases

These five requests retain the full classes H, E₁+L and E₂+L. Their complete
three-column expansions are checked against separately stated basis labels.
The equations will determine the ruling and L values from the existing seeds.
No numerical invariant value is used to check a coefficient identity.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceBlowupWDVV

open SurfacePolynomialReduction

/-- The H,pt,E,E request in class H=E+F on F₁. -/
def hirzebruchLine : RationalTerms (Variable .hirzebruchOne) :=
  RationalTerms.term 1
    (↑([.inr (SurfaceQuery.points .hirzebruchOne 0 ![0, 1] 1),
      .inr (SurfaceQuery.points .hirzebruchOne 0 ![1, 0] 0)] : List (Variable .hirzebruchOne)) :
      Multiset (Variable .hirzebruchOne)) +
  RationalTerms.term (-1) {.inr (SurfaceQuery.points .hirzebruchOne 0 ![1, 1] 2)}

/-- The H,H,pt,E₁ request isolates a product involving E₁+E₂. -/
def mixedLine : RationalTerms (Variable .blowupTwo) :=
  RationalTerms.term (-2)
    (↑([.inr (SurfaceQuery.points .blowupTwo 0 ![0, 0, 1] 0),
      .inr (SurfaceQuery.points .blowupTwo 0 ![1, 1, 0] 1)] : List (Variable .blowupTwo)) :
      Multiset (Variable .blowupTwo))

/-- The H,pt,E₁,E₁ request relates H to E₁ and the ruling E₂+L. -/
def line : RationalTerms (Variable .blowupTwo) :=
  RationalTerms.term 2
    (↑([.inr (SurfaceQuery.points .blowupTwo 0 ![0, 0, 1] 0),
      .inr (SurfaceQuery.points .blowupTwo 0 ![1, 1, 0] 1)] : List (Variable .blowupTwo)) :
      Multiset (Variable .blowupTwo)) +
  RationalTerms.term 1
    (↑([.inr (SurfaceQuery.points .blowupTwo 0 ![0, 1, 1] 1),
      .inr (SurfaceQuery.points .blowupTwo 0 ![1, 0, 0] 0)] : List (Variable .blowupTwo)) :
      Multiset (Variable .blowupTwo)) +
  RationalTerms.term (-1) {.inr (SurfaceQuery.points .blowupTwo 0 ![1, 1, 1] 2)}

/-- The H,H,Eᵢ,Eᵢ request in full class Eᵢ+L, for either exceptional divisor. -/
def ruling (i : Fin 2) : RationalTerms (Variable .blowupTwo) :=
  RationalTerms.term 1
    (↑([.inr (SurfaceQuery.points .blowupTwo 0 ![0, 0, 1] 0),
      .inr (SurfaceQuery.points .blowupTwo 0 (SurfaceTarget.blowupTwo.exceptionalCurve i) 0)] :
      List (Variable .blowupTwo)) : Multiset (Variable .blowupTwo)) +
  RationalTerms.term (-1) {.inr (SurfaceQuery.points .blowupTwo 0
    (SurfaceTarget.blowupTwo.exceptionalCurve i + ![0, 0, 1]) 1)}

/-- Exact expansion of the F₁ line request. -/
theorem hirzebruchLine_accepted : RationalTerms.Equivalent
    (WDVV.primaryTerms .hirzebruchOne 0 ![1, 1] 0
      ![.hyperplane, .point, .exceptional 0, .exceptional 0]) hirzebruchLine := by
  decide +kernel

/-- Exact expansion of the mixed line request on the two-point blowup. -/
theorem mixedLine_accepted : RationalTerms.Equivalent
    (WDVV.primaryTerms .blowupTwo 0 ![1, 1, 1] 0
      ![.hyperplane, .hyperplane, .point, .exceptional 0]) mixedLine := by
  decide +kernel

/-- Exact expansion of the line normalization equation. -/
theorem line_accepted : RationalTerms.Equivalent
    (WDVV.primaryTerms .blowupTwo 0 ![1, 1, 1] 0
      ![.hyperplane, .point, .exceptional 0, .exceptional 0]) line := by
  decide +kernel

/-- Each ruling equation is checked at its own full class and exceptional label. -/
theorem ruling_accepted (i : Fin 2) : RationalTerms.Equivalent
    (WDVV.primaryTerms .blowupTwo 0 (SurfaceTarget.blowupTwo.exceptionalCurve i + ![0, 0, 1]) 0
      ![.hyperplane, .hyperplane, .exceptional i, .exceptional i]) (ruling i) := by
  fin_cases i <;> decide +kernel

end AxiomaticGW.SurfaceBlowupWDVV
