/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNRelation
public import AxiomaticGW.Surfaces.GenusTwoBlowupValuation

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoBlowupNRelation
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupNRelation

/-- Changing every ancestor callback has no effect on the complete combined equation. -/
public theorem ancestor_callback_independent (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (a b : SurfaceAncestorKey X → ℚ) (v : SurfaceQuery X → ℚ) :
    RationalTerms.eval (Sum.elim a v) (row X i beta) =
      RationalTerms.eval (Sum.elim b v) (row X i beta) := by
  apply eval_row_congr_canonical i beta
  intro gamma _ c _
  rfl

/-- The actual four-row equation can be evaluated using an exact canonical table. -/
public theorem row_uses_canonical_table (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (v : Variable X → ℚ) :
    RationalTerms.eval v (row X i beta) =
      RationalTerms.eval (canonicalValuation (fun s ↦ v (.inr (s.2.query s.1))))
        (row X i beta) := by
  apply eval_row_congr_canonical i beta
  intro gamma _ c hc
  obtain ⟨f, rfl⟩ := family_of_mem_canonicalQueries hc
  rw [canonicalValuation_query]

/-- Applying the original BP equations at the shifted source derives the combination. -/
public theorem original_equations_suffice (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (v : Variable X → ℚ)
    (h : ∀ a : Fin 3 → SurfaceBasisLabel X,
      RationalTerms.eval v (BelorousskiPandharipande.normalizedGenusTwoTerms X
        (X.effective.energy beta) (beta + X.exceptionalCurve i) 0
        (SurfaceGenusZero.pointLabels a (X.effective.energy beta))) = 0) :
    RationalTerms.eval v (row X i beta) = 0 :=
  eval_row_eq_zero i beta v (h _) (h _) (h _) (h _)

/-- The nominal zero-class target is covered by closure without claiming a nonzero pivot. -/
public theorem zero_target_closure (X : SurfaceTarget) (i : Fin X.blowups)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ RationalTerms.collect (row X i 0)) :
    t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ c ∈ SurfaceGenusTwo.canonicalQueries X gamma,
      t.2 = {Sum.inr c} ∧ ∃ delta : X.Curve, gamma + delta = X.exceptionalCurve i := by
  simpa only [zero_add] using collected_row_canonical_support i 0 ht

end AxiomaticGWTest.Surfaces.GenusTwoBlowupNRelation
