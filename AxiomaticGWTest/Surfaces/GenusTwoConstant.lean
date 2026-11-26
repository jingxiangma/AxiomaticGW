/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoL24Constant

/-! Zero-valuation constant replay keeps nonzero calibration tails and higher ancestor tags. -/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoConstant
open AxiomaticGW SurfacePolynomialReduction

/-- Reducible pure exceptional class 2E with its genuine first-calibration correction. -/
def exceptionalTail : SurfaceAncestorKey .hirzebruchOne :=
  SurfaceAncestorKey.ofLabels 2 (Fin 3) (by unfold StableArity; decide +kernel) ![2, 0]
    ![1, 0, 0] ![.exceptional 0, .point, .point]

/-- The signed smaller-class tail remains nonzero in the original normalized polynomial. -/
theorem exceptional_tail_coefficient : RationalTerms.coefficient (normalizedTerms exceptionalTail)
    {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![1, 0] 2)} = -1 := by
  decide +kernel

/-- Constant extraction sets residual variables to zero without deleting the actual tail. -/
theorem exceptional_tail_zero_valuation :
    RationalTerms.eval (fun _ ↦ (0 : ℚ)) (normalizedTerms exceptionalTail) = 0 :=
  eval_zero_normalizedTerms exceptionalTail (by decide +kernel)

/-- The zero scalar above is not a proof that the signed normalized polynomial vanishes. -/
theorem exceptional_tail_polynomial_ne_zero : normalizedTerms exceptionalTail ≠ 0 := by
  intro h
  have hc := exceptional_tail_coefficient
  rw [h, RationalTerms.coefficient_zero] at hc
  norm_num at hc

/-- A stable class-zero higher-power request at genus three remains an ancestor variable. -/
def higherAncestor : SurfaceAncestorKey .blowupTwo :=
  SurfaceAncestorKey.ofLabels 3 (Fin 1) (by unfold StableArity; decide +kernel) 0
    ![3] ![.unit]

/-- The generic constant theorem does not silently normalize higher powers into descendants. -/
theorem higher_ancestor_coefficient : RationalTerms.coefficient (normalizedTerms higherAncestor)
    {Sum.inl higherAncestor} = 1 := by
  decide +kernel

/-- Genus above two and higher powers still have zero residual-variable constant. -/
theorem higher_ancestor_zero_valuation :
    RationalTerms.eval (fun _ ↦ (0 : ℚ)) (normalizedTerms higherAncestor) = 0 :=
  eval_zero_normalizedTerms higherAncestor (by decide +kernel)

/-- Arbitrary external powers on a negative-multiplicity full class preserve the BP constant. -/
theorem blowup_bp_arbitrary_powers (n : ℕ) (k : ExtraMarkings n (Fin 3) → ℕ)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel .blowupTwo) :
    RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo n ![2, 0, 1] k a) =
      RationalTerms.eval (fun _ ↦ (0 : ℚ))
        (BelorousskiPandharipande.genusTwoTerms .blowupTwo n ![2, 0, 1] k a) :=
  BelorousskiPandharipande.eval_zero_normalizedGenusTwoTerms .blowupTwo n ![2, 0, 1] k a

/-- The complete decorated L24 row also preserves constants at arbitrary powers and counts. -/
theorem blowup_l24_arbitrary_powers (n : ℕ) (beta : SurfaceTarget.hirzebruchOne.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel .hirzebruchOne) :
    RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (L24Relation.normalizedGenusTwoTerms .hirzebruchOne n beta k a) =
      RationalTerms.eval (fun _ ↦ (0 : ℚ))
        (L24Relation.genusTwoTerms .hirzebruchOne n beta k a) :=
  L24Relation.eval_zero_normalizedGenusTwoTerms .hirzebruchOne n beta k a

/-- BP scalar contraction is tied to its original full normalized row on F1. -/
theorem f1_bp_compressed_constant (n : ℕ) (beta : SurfaceTarget.hirzebruchOne.Curve) :
    BelorousskiPandharipande.pointConstant .hirzebruchOne n beta
      ![.exceptional 0, .hyperplane, .hyperplane] =
      RationalTerms.eval (fun _ ↦ (0 : ℚ))
        (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne n beta 0
          (SurfaceGenusZero.pointLabels ![.exceptional 0, .hyperplane, .hyperplane] n)) :=
  BelorousskiPandharipande.pointConstant_eq_normalized .hirzebruchOne n beta _

/-- L24 scalar contraction preserves distinct exceptional labels and repeated states. -/
theorem bl2_l24_compressed_constant (n : ℕ) (beta : SurfaceTarget.blowupTwo.Curve) :
    L24Relation.pointConstant .blowupTwo n beta
      ![.hyperplane, .exceptional 0, .exceptional 1, .exceptional 0] =
      RationalTerms.eval (fun _ ↦ (0 : ℚ))
        (L24Relation.normalizedGenusTwoTerms .blowupTwo n beta 0
          (SurfaceGenusZero.pointLabels
            ![.hyperplane, .exceptional 0, .exceptional 1, .exceptional 0] n)) :=
  L24Relation.pointConstant_eq_normalized .blowupTwo n beta _

/-- The existing plane scalar interface retains its complete original type and value. -/
theorem plane_api_preserved (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) :
    BelorousskiPandharipande.pointConstant .plane n beta a =
      RationalTerms.eval (fun _ ↦ (0 : ℚ))
        (BelorousskiPandharipande.normalizedGenusTwoTerms .plane n beta 0
          (SurfaceGenusZero.pointLabels a n)) :=
  BelorousskiPandharipande.pointConstant_plane_eq n beta a

end AxiomaticGWTest.SurfaceGenusTwoConstant
