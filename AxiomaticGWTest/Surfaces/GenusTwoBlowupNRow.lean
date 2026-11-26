/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNRow
public import AxiomaticGW.Surfaces.GenusTwoBlowupValuation

/-! Consumers of the solved primary row, its sign, full-class support and valuation boundary. -/

@[expose] public section
namespace AxiomaticGWTest.SurfaceGenusTwoBlowupNRow
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupNRow

/-- A negative signed multiplicity uses the unchanged negative remainder over six. -/
theorem negative_multiplicity_sign (v : Variable .blowupTwo → ℚ)
    (he : RationalTerms.eval v (SurfaceGenusTwoBlowupNRelation.row .blowupTwo 0
      ![2, 0, 1]) = 0) :
    v (.inr (Family.primary.query (![2, 0, 1] : SurfaceTarget.blowupTwo.Curve))) =
      -RationalTerms.eval v (remainder .blowupTwo 0 ![2, 0, 1]) / 6 := by
  have h := value_eq_step .blowupTwo 0 v ![2, 0, 1] (by decide +kernel) he
  rw [step, show SurfaceTarget.blowupTwo.planeDegree ![2, 0, 1] = 1 from rfl,
    Nat.cast_one, mul_one] at h
  exact h

/-- At plane degree two the denominator is twelve, including zero exceptional multiplicity. -/
theorem degree_two_denominator (v : Variable .hirzebruchOne → ℚ)
    (he : RationalTerms.eval v (SurfaceGenusTwoBlowupNRelation.row .hirzebruchOne 0
      ![2, 2]) = 0) :
    v (.inr (Family.primary.query (![2, 2] : SurfaceTarget.hirzebruchOne.Curve))) =
      -RationalTerms.eval v (remainder .hirzebruchOne 0 ![2, 2]) / 12 := by
  have h := value_eq_step .hirzebruchOne 0 v ![2, 2] (by decide +kernel) he
  rw [step, show SurfaceTarget.hirzebruchOne.planeDegree ![2, 2] = 2 from rfl,
    Nat.cast_ofNat, show (6 : ℚ) * 2 = 12 from by norm_num] at h
  exact h

/-- Arbitrary changes to every ancestor value cannot change the reconstructed primary step. -/
theorem ancestor_callback_independent (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (v : SurfaceQuery X → ℚ) (a b : SurfaceAncestorKey X → ℚ) :
    step X i (Sum.elim a v) beta = step X i (Sum.elim b v) beta := by
  apply step_congr X i _ _ beta
  intro gamma family _
  rfl

/-- Exact canonical table extension suffices for the original complete primary step. -/
theorem canonical_table_suffices (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (v : Variable X → ℚ) :
    step X i v beta =
      step X i (canonicalValuation (fun s ↦ v (.inr (s.2.query s.1)))) beta := by
  apply step_congr X i _ _ beta
  intro gamma family _
  rw [canonicalValuation_query]

/-- The two exceptional shifts agree under their original equations without identifying classes. -/
theorem two_exceptional_shifts (v : Variable .blowupTwo → ℚ)
    (he : RationalTerms.eval v (SurfaceGenusTwoBlowupNRelation.row .blowupTwo 0
      ![1, 0, 1]) = 0)
    (hf : RationalTerms.eval v (SurfaceGenusTwoBlowupNRelation.row .blowupTwo 1
      ![1, 0, 1]) = 0) :
    step .blowupTwo 0 v ![1, 0, 1] = step .blowupTwo 1 v ![1, 0, 1] :=
  step_eq_of_rows .blowupTwo 0 1 v ![1, 0, 1] (by decide +kernel) he hf

end AxiomaticGWTest.SurfaceGenusTwoBlowupNRow
