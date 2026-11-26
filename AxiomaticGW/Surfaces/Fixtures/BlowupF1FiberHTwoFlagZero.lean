/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroCoefficients

/-! # Exact two-flag zeros for the class-zero first-descendant requests

The small component check preserves every divisor label and point count used
by the original one-point pullback. The existing one-psi coefficient theorem
removes only proved-zero primary tails, retaining the complete original
coefficient and arbitrary effective remainder.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberHTwoFlagZero
open SurfacePolynomialReduction SurfaceGenusTwo BlowupF1FiberHReduction
open BlowupF1FiberHZeroCoefficients
set_option maxRecDepth 20000

/-- The two requested divisor labels remain separate. -/
def requested (r : Fin 2) : SurfaceBasisLabel target :=
  if r = 0 then .hyperplane else .exceptional 0

/-- Exhaustive small component coefficient check: both flags, both point counts and all labels. -/
theorem component_checked : ∀ (r n s : Fin 2) (a₀ a₁ : SurfaceBasisLabel target),
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (residualTerms ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity])
        (0 : target.Curve) (Pi.single s 1) ![a₀, a₁]).addPoints n.val)))
      {zeroVariable (requested r)} = 0 := by
  decide +kernel

/-- At either used point count, the exact genus-two two-flag component coefficient is zero.
The arbitrary remainder is handled by the existing class-support theorem. -/
theorem remainder_two_flags_zero (r : Fin 2) (n : ℕ) (hn : n ≤ 1)
    (s : Fin 2) (h : StableArity 2 (Fin 2)) (delta : target.Curve)
    (a : Fin 2 → SurfaceBasisLabel target) :
    remainderVertex target (zeroVariable (requested r))
      (firstCoefficientVertex target 0 (requested r) 0) n 2 (Fin 2) h
      (Pi.single s 1) inferInstance delta a = 0 := by
  have hv : ∀ beta m, Sum.inr (SurfaceQuery.points target 2 beta m) ≠
      zeroVariable (requested r) := fun beta m ↦
    SurfaceFirstDescendant.query_ne_points 0 beta (requested r) 0 m
  rw [firstCoefficientVertex_eq]
  change remainderVertex target (zeroVariable (requested r))
    (coefficientVertex target (zeroVariable (requested r))) n 2 (Fin 2) h
      (Pi.single s 1) inferInstance delta a = 0
  rw [remainderVertex_onePsi_of_not_points
    (zeroVariable (requested r)) hv n (Fin 2) h s delta a]
  split_ifs
  · have ha : a = ![a 0, a 1] := by
      funext k
      fin_cases k <;> rfl
    rw [ha]
    exact component_checked r ⟨n, by omega⟩ s (a 0) (a 1)
  · rfl

end AxiomaticGW.BlowupF1FiberHTwoFlagZero
