/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoLineCanonical
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLinePrimary
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineHConstant

/-!
# Comparing the five canonical strict-line queries with GKM localization

The exact discrepancy between reconstruction and the incoming ordinary
value is the same for H, P, N, K₁ and K₂. It reduces to the original
shifted lower-genus L24 sum minus 7/2880.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoLineCanonical
open SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction BlowupTwoLineBP

/-- Positions of H, P, K₁ and K₂ among the five incoming canonical queries. -/
def descendantIndex : Fin 4 → Fin 5 := ![0, 1, 3, 4]

/-- On the entire request frame the discrepancy is given by the original lower-genus sum. -/
theorem discrepancy (i : Fin 5) :
    canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0) (.inr (requests i)) -
      values i = (∑ j, BlowupTwoLineH.weighted j) - 7 / 2880 := by
  rw [coverage, canonicalValuation_query, ← BlowupTwoLineH.constant_eq_sum,
    ← BlowupTwoLineH.value_eq_constant_sub]
  have hv : values i = 0 := by fin_cases i <;> decide +kernel
  rw [hv, sub_zero]
  exact family_eq_hyperplane _

/-- Specialization to the four canonical descendants. -/
theorem descendant_discrepancy (j : Fin 4) :
    canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0)
      (.inr (requests (descendantIndex j))) - values (descendantIndex j) =
      (∑ i, BlowupTwoLineH.weighted i) - 7 / 2880 :=
  discrepancy (descendantIndex j)

end AxiomaticGW.GKM.BlowupTwoLineCanonical
