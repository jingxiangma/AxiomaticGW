/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoNormalizedBP
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoBP

/-!
# Kernel replay of normalized genus-two surface equations

The held ancestor polynomials are bound to the original BP expansion by
whole-equation checks. Their first-descendant normalization is replayed
separately, retaining all constants and variable interpretations.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoNormalizedBP
open SurfacePolynomialReduction SurfaceFirstDescendant BelorousskiPandharipande

set_option Elab.async false

theorem planeZero_normalized : RationalTerms.Equivalent
    (RationalTerms.affineSubstitute normalizedTerms SurfaceGenusTwoBP.planeZero) 0 := by
  decide +kernel

/-- The exceptional equation has two same-class first-descendant unknowns. -/
def exceptional : RationalTerms (Variable .hirzebruchOne) :=
  RationalTerms.term (-1/240) 0 +
  RationalTerms.term 12 {.inr (SurfaceQuery.points .hirzebruchOne 2 0 1)} +
  RationalTerms.term (-12) {.inr (query 2 0 (.exceptional 0) 0)} +
  RationalTerms.term (-18) {.inr (query 2 ![1,0] (.exceptional 0) 1)} +
  RationalTerms.term (-18) {.inr (query 2 ![1,0] .point 0)}

theorem exceptional_normalized : RationalTerms.Equivalent
    (RationalTerms.affineSubstitute normalizedTerms SurfaceGenusTwoBP.exceptional) exceptional := by
  decide +kernel

/-- The E₁ state at E₂ leaves a single descendant query, with the classes distinct. -/
def distinctExceptional : RationalTerms (Variable .blowupTwo) :=
  RationalTerms.term (-18) {.inr (query 2 ![0,1,0] (.exceptional 0) 1)}

theorem distinctExceptional_normalized : RationalTerms.Equivalent
    (RationalTerms.affineSubstitute normalizedTerms SurfaceGenusTwoBP.distinctExceptional)
    distinctExceptional := by decide +kernel

/-- The complete held L₁₂ equation with states E₁,E₂,H, before normalization. -/
def blowupTwoLineAncestor : RationalTerms (SurfaceAncestorKey .blowupTwo) :=
  RationalTerms.term (1/240) 0 +
  RationalTerms.term (-12) {⟨2, 0, {⟨.point, 0⟩}, by decide +kernel⟩} +
  RationalTerms.term (-12) {⟨2, 0, {⟨.exceptional 0, 1⟩}, by decide +kernel⟩} +
  RationalTerms.term (-12) {⟨2, 0, {⟨.exceptional 1, 1⟩}, by decide +kernel⟩} +
  RationalTerms.term (-12) {⟨2, 0, {⟨.hyperplane, 1⟩, ⟨.exceptional 0, 0⟩},
    by decide +kernel⟩} +
  RationalTerms.term (-12) {⟨2, 0, {⟨.hyperplane, 1⟩, ⟨.exceptional 1, 0⟩},
    by decide +kernel⟩} +
  RationalTerms.term 12 {⟨2, 0, {⟨.hyperplane, 1⟩}, by decide +kernel⟩} +
  RationalTerms.term 12 {⟨2, 0, {⟨.hyperplane, 0⟩, ⟨.exceptional 0, 1⟩},
    by decide +kernel⟩} +
  RationalTerms.term 12 {⟨2, 0, {⟨.hyperplane, 0⟩, ⟨.exceptional 1, 1⟩},
    by decide +kernel⟩}

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- The kernel expands all twenty BP diagrams and six original label assignments.
/-- All original BP terms, assignments and signed splittings are checked in the kernel. -/
theorem blowupTwoLineAncestor_checked : RationalTerms.Equivalent
    (genusTwoTerms .blowupTwo 0 ![0,0,1] 0 ![.exceptional 0, .exceptional 1, .hyperplane])
    blowupTwoLineAncestor := by decide +kernel

/-- This equation contains only the original degree-zero seed sector and the primary point. -/
def blowupTwoLine : RationalTerms (Variable .blowupTwo) :=
  RationalTerms.term (1/240) 0 +
  RationalTerms.term (-12) {.inr (SurfaceQuery.points .blowupTwo 2 0 1)} +
  RationalTerms.term (-12) {.inr (query 2 0 (.exceptional 0) 0)} +
  RationalTerms.term (-12) {.inr (query 2 0 (.exceptional 1) 0)} +
  RationalTerms.term 12 {.inr (query 2 0 .hyperplane 0)}

theorem blowupTwoLine_normalized : RationalTerms.Equivalent
    (RationalTerms.affineSubstitute normalizedTerms blowupTwoLineAncestor) blowupTwoLine := by
  decide +kernel

/-- Bind the compact E₂ equation to its whole original BP expansion under any valuation. -/
theorem eval_distinctExceptional (v : Variable .blowupTwo → ℚ) :
    RationalTerms.eval v (normalizedGenusTwoTerms .blowupTwo 0 ![0,1,0] 0
      (fun _ ↦ .exceptional 0)) = RationalTerms.eval v distinctExceptional := by
  rw [normalizedGenusTwoTerms, RationalTerms.eval_affineSubstitute_eq_of_equivalent v
    normalizedTerms _ _ SurfaceGenusTwoBP.distinctExceptional_checked
    (genusTwoTerms_card_le_one _ _ _ _ _) (by decide +kernel)]
  exact RationalTerms.eval_eq_of_equivalent v _ _ distinctExceptional_normalized

/-- Bind the compact degree-zero equation to its whole original BP expansion. -/
theorem eval_blowupTwoLine (v : Variable .blowupTwo → ℚ) :
    RationalTerms.eval v (normalizedGenusTwoTerms .blowupTwo 0 ![0,0,1] 0
      ![.exceptional 0, .exceptional 1, .hyperplane]) = RationalTerms.eval v blowupTwoLine := by
  rw [normalizedGenusTwoTerms, RationalTerms.eval_affineSubstitute_eq_of_equivalent v
    normalizedTerms _ _ blowupTwoLineAncestor_checked
    (genusTwoTerms_card_le_one _ _ _ _ _) (by decide +kernel)]
  exact RationalTerms.eval_eq_of_equivalent v _ _ blowupTwoLine_normalized

end AxiomaticGW.SurfaceGenusTwoNormalizedBP
