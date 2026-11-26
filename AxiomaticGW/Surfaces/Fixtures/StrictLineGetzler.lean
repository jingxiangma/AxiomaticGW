/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.TermExpansion

/-!
# Checked Getzler equations for twice L = H−E₁−E₂

Unlike E₁ and E₂, L is the final effective generator. Its three selected
requests have different coefficients, computed with its own full curve class
and the unchanged surface metric. No identification with an exceptional
coordinate or extra numerical seed is used.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceStrictLineGetzler

open SurfacePolynomialReduction

/-- Three unknown monomials, with explicit rational candidate coefficients. -/
def terms (x y z : ℚ) : RationalTerms (Variable .blowupTwo) :=
  RationalTerms.term x
    (↑([.inr (SurfaceQuery.points .blowupTwo 0 ![0, 0, 1] 0),
      .inr (SurfaceQuery.points .blowupTwo 1 ![0, 0, 1] 1)] : List (Variable .blowupTwo)) :
      Multiset (Variable .blowupTwo)) +
  RationalTerms.term y {.inr (SurfaceQuery.points .blowupTwo 0 ![0, 0, 2] 1)} +
  RationalTerms.term z {.inr (SurfaceQuery.points .blowupTwo 1 ![0, 0, 2] 2)}

set_option maxHeartbeats 0 in
-- Exact finite graph expansion requires a larger kernel-reduction budget.
set_option maxRecDepth 65536 in
/-- Four hyperplanes retain the genus-one two-point value of 2L. -/
theorem hyperplane_accepted : RationalTerms.Equivalent
    (GetzlerGraphs.primaryTerms .blowupTwo 0 ![0, 0, 2] 0 (fun _ ↦ .hyperplane))
    (terms 24 (-5) (-9)) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Exact finite graph expansion requires a larger kernel-reduction budget.
set_option maxRecDepth 65536 in
/-- H,H,H,E₁ gives the first equation in the two remaining unknowns. -/
theorem threeHyperplanes_accepted : RationalTerms.Equivalent
    (GetzlerGraphs.primaryTerms .blowupTwo 0 ![0, 0, 2] 0
      ![.hyperplane, .hyperplane, .hyperplane, .exceptional 0])
    (terms 15 (-11 / 2) 0) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Exact finite graph expansion requires a larger kernel-reduction budget.
set_option maxRecDepth 65536 in
/-- H,E₁,E₁,E₁ gives an independent second equation in those unknowns. -/
theorem oneHyperplane_accepted : RationalTerms.Equivalent
    (GetzlerGraphs.primaryTerms .blowupTwo 0 ![0, 0, 2] 0
      ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0])
    (terms (-3) (-13 / 2) 0) := by
  decide +kernel

end AxiomaticGW.SurfaceStrictLineGetzler
