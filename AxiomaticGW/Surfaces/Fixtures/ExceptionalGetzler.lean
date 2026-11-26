/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.TermExpansion

/-!+# Checked Getzler equations for twice an exceptional class

The three requests have full class `2Eᵢ`, no added markings, zero powers,
and external labels HHHH, HEᵢEᵢEᵢ, and HHEᵢEᵢ. The candidate terms were
found by exact Sage exploration. Kernel checks compare them to the complete
33-column evaluator for every exceptional divisor on the two fixed blowups.
No geometric vanishing or numerical seed is used in these coefficient checks.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceExceptionalGetzler

open SurfacePolynomialReduction

/-- Candidate for four hyperplane insertions in class `2Eᵢ`. -/
def hyperplaneTerms (X : SurfaceTarget) (i : Fin X.blowups) : RationalTerms (Variable X) :=
  RationalTerms.term (-9) {.inr (SurfaceQuery.points X 1 (2 • X.exceptionalCurve i) 2)}

/-- Candidate for one hyperplane and three exceptional-divisor insertions. -/
def oneHyperplaneTerms (X : SurfaceTarget) (i : Fin X.blowups) : RationalTerms (Variable X) :=
  RationalTerms.term (-3 / 2) {.inr (SurfaceQuery.points X 0 (2 • X.exceptionalCurve i) 1)}

/-- The mixed equation retains the product of the two class-`Eᵢ` invariants. -/
def twoHyperplaneTerms (X : SurfaceTarget) (i : Fin X.blowups) : RationalTerms (Variable X) :=
  RationalTerms.term 3
    (↑([.inr (SurfaceQuery.points X 0 (X.exceptionalCurve i) 0),
      .inr (SurfaceQuery.points X 1 (X.exceptionalCurve i) 1)] : List (Variable X)) :
      Multiset (Variable X)) +
  RationalTerms.term (-1 / 6) {.inr (SurfaceQuery.points X 0 (2 • X.exceptionalCurve i) 1)} +
  RationalTerms.term 3 {.inr (SurfaceQuery.points X 1 (2 • X.exceptionalCurve i) 2)}

set_option maxHeartbeats 0 in
-- Exact finite graph expansion requires a larger kernel-reduction budget.
set_option maxRecDepth 65536 in
/-- HHHH gives precisely the proposed singleton equation. -/
theorem hyperplaneTerms_accepted (X : SurfaceTarget) (i : Fin X.blowups) :
    RationalTerms.Equivalent
      (GetzlerGraphs.primaryTerms X 0 (2 • X.exceptionalCurve i) 0 (fun _ ↦ .hyperplane))
      (hyperplaneTerms X i) := by
  cases X <;> fin_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
-- Exact finite graph expansion requires a larger kernel-reduction budget.
set_option maxRecDepth 65536 in
/-- HEᵢEᵢEᵢ isolates the genus-zero one-point invariant of `2Eᵢ`. -/
theorem oneHyperplaneTerms_accepted (X : SurfaceTarget) (i : Fin X.blowups) :
    RationalTerms.Equivalent
      (GetzlerGraphs.primaryTerms X 0 (2 • X.exceptionalCurve i) 0
        ![.hyperplane, .exceptional i, .exceptional i, .exceptional i])
      (oneHyperplaneTerms X i) := by
  cases X <;> fin_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
-- Exact finite graph expansion requires a larger kernel-reduction budget.
set_option maxRecDepth 65536 in
/-- HHEᵢEᵢ has the three stated coefficients, including the split product. -/
theorem twoHyperplaneTerms_accepted (X : SurfaceTarget) (i : Fin X.blowups) :
    RationalTerms.Equivalent
      (GetzlerGraphs.primaryTerms X 0 (2 • X.exceptionalCurve i) 0
        ![.hyperplane, .hyperplane, .exceptional i, .exceptional i])
      (twoHyperplaneTerms X i) := by
  cases X <;> fin_cases i <;> decide +kernel

end AxiomaticGW.SurfaceExceptionalGetzler
