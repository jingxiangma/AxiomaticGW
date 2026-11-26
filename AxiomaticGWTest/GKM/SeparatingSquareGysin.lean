/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeSeparatingSquare

/-! The nonunit elliptic factors detect the exchange hidden by unit specialization. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.SeparatingSquareGysin

open AxiomaticGW AxiomaticGW.GKM.LoopSeparatingGysin AxiomaticGW.GKM.SeparatingSquareGysin
open scoped TensorProduct

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

/-- Direct rational-label test: every positive psi class on Mbar(0,3) vanishes. -/
theorem rational_node_labels :
    centralExchange none = some none ∧ centralExchange (some none) = none ∧
      centralExchange (some (some 0)) = some (some 0) := centralExchange_labels

/-- Arbitrary independent elliptic insertions change order under the other contraction. -/
theorem elliptic_factor_exchange (b c : C.H 1 UnmarkedLabels) :
    refinementExchange C (1 ⊗ₜ[R] (b ⊗ₜ[R] c)) = 1 ⊗ₜ[R] (c ⊗ₜ[R] b) := by
  rw [refinementExchange_tmul, map_one]

/-- A nonunit class on the original unmarked source moves to the other elliptic tail. -/
theorem other_unmarked_insertion (y : C.H 1 UnmarkedLabels) :
    refinementOtherPull C (1 ⊗ₜ[R] y) = 1 ⊗ₜ[R] (y ⊗ₜ[R] 1) := by
  unfold refinementOtherPull refinementPull
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, map_one]
  change refinementExchange C (1 ⊗ₜ[R] (1 ⊗ₜ[R] y)) = _
  rw [refinementExchange_tmul, map_one]

theorem other_unmarked_psi (P : PsiClasses C) :
    refinementOtherPull C (1 ⊗ₜ[R] P.psi 1 UnmarkedLabels unmarkedStable none) =
      1 ⊗ₜ[R] (P.psi 1 UnmarkedLabels unmarkedStable none ⊗ₜ[R] 1) :=
  other_unmarked_insertion _

/-- Arbitrary product factors remain in the derived projection formula. -/
theorem arbitrary_insertions (F : SeparatingPushforward C I) (P : PsiClasses C)
    (H : SelfGysinCompatible F P) (z w : Source C) :
    separatingPush F z * separatingPush F w =
      separatingPush F ((z * normalClass P +
        refinementPush F (refinementOtherPull C z)) * w) :=
  product_of_selfGysin F P H z w

end AxiomaticGWTest.GKM.SeparatingSquareGysin
