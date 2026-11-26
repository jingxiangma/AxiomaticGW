/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module
public import AxiomaticGW.Surfaces.GenusTwoBlowupNCoefficients
@[expose] public section
namespace AxiomaticGWTest.SurfaceGenusTwoBlowupNCoefficients
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupNRelation
open SurfaceGenusTwoBlowupNCoefficients

/-- Negative signed multiplicity leaves the actual N pivot nonzero. -/
theorem negative_multiplicity_pivot :
    RationalTerms.coefficient (row SurfaceTarget.blowupTwo 0 ![2, 0, 1])
      {Sum.inr (SurfaceQuery.points SurfaceTarget.blowupTwo 2 ![2, 0, 1]
        (SurfaceTarget.blowupTwo.effective.energy ![2, 0, 1] + 1))} = 6 :=
  (row_primary_coefficient 0 (![2, 0, 1] : SurfaceTarget.blowupTwo.Curve)).trans
    (by decide +kernel)

/-- The zero exceptional-multiplicity boundary retains the actual primary pivot. -/
theorem zero_multiplicity_pivot :
    RationalTerms.coefficient (row SurfaceTarget.blowupTwo 0 ![1, 0, 1])
      {Sum.inr (SurfaceQuery.points SurfaceTarget.blowupTwo 2 ![1, 0, 1]
        (SurfaceTarget.blowupTwo.effective.energy ![1, 0, 1] + 1))} = 6 :=
  (row_primary_coefficient 0 (![1, 0, 1] : SurfaceTarget.blowupTwo.Curve)).trans
    (by decide +kernel)

/-- A degree-two F1 class distinguishes the linear plane-degree factor. -/
theorem hirzebruch_degree_two_pivot :
    RationalTerms.coefficient (row SurfaceTarget.hirzebruchOne 0 ![0, 2])
      {Sum.inr (SurfaceQuery.points SurfaceTarget.hirzebruchOne 2 ![0, 2]
        (SurfaceTarget.hirzebruchOne.effective.energy ![0, 2] + 1))} = 12 :=
  (row_primary_coefficient 0 (![0, 2] : SurfaceTarget.hirzebruchOne.Curve)).trans
    (by decide +kernel)

/-- A degree-three second blowup class distinguishes 6d from 6d squared. -/
theorem blowup_degree_three_pivot :
    RationalTerms.coefficient (row SurfaceTarget.blowupTwo 0 ![0, 0, 3])
      {Sum.inr (SurfaceQuery.points SurfaceTarget.blowupTwo 2 ![0, 0, 3]
        (SurfaceTarget.blowupTwo.effective.energy ![0, 0, 3] + 1))} = 18 :=
  (row_primary_coefficient 0 (![0, 0, 3] : SurfaceTarget.blowupTwo.Curve)).trans
    (by decide +kernel)

/-- The combined coefficient at degree-zero N is zero; no exceptional pivot is inferred. -/
theorem exceptional_degree_zero_pivot :
    RationalTerms.coefficient (row SurfaceTarget.hirzebruchOne 0 ![1, 0])
      {Sum.inr (SurfaceQuery.points SurfaceTarget.hirzebruchOne 2 ![1, 0]
        (SurfaceTarget.hirzebruchOne.effective.energy ![1, 0] + 1))} = 0 :=
  (row_primary_coefficient 0 (![1, 0] : SurfaceTarget.hirzebruchOne.Curve)).trans
    (by decide +kernel)

/-- The class-zero boundary is retained with its actual zero primary coefficient. -/
theorem class_zero_pivot :
    RationalTerms.coefficient (row SurfaceTarget.blowupTwo 0 0)
      {Sum.inr (SurfaceQuery.points SurfaceTarget.blowupTwo 2 0
        (SurfaceTarget.blowupTwo.effective.energy 0 + 1))} = 0 :=
  (row_primary_coefficient 0 (0 : SurfaceTarget.blowupTwo.Curve)).trans (by decide +kernel)

/-- The EHH primary coefficient retains the sign of a negative exceptional intersection. -/
theorem negative_multiplicity_ehh :
    BelorousskiPandharipande.pointCoefficient SurfaceTarget.blowupTwo
      (SurfaceTarget.blowupTwo.effective.energy ![2, 0, 1])
      (![2, 0, 1] + SurfaceTarget.blowupTwo.exceptionalCurve 0)
      ![.exceptional 0, .hyperplane, .hyperplane]
      (.inr (SurfaceQuery.points SurfaceTarget.blowupTwo 2 ![2, 0, 1]
        (SurfaceTarget.blowupTwo.effective.energy ![2, 0, 1] + 1))) = -6 :=
  (pointCoefficient_ehh_primary_shifted 0 (![2, 0, 1] : SurfaceTarget.blowupTwo.Curve)).trans
    (by decide +kernel)

/-- Every exceptional label at the shifted source cancels as a full query. -/
theorem source_exceptional_label_cancel (j : Fin SurfaceTarget.blowupTwo.blowups) :
    let beta : SurfaceTarget.blowupTwo.Curve := ![1, 0, 1]
    let sigma := beta + SurfaceTarget.blowupTwo.exceptionalCurve 0
    RationalTerms.coefficient (row SurfaceTarget.blowupTwo 0 beta)
      {Sum.inr (SurfaceFirstDescendant.query 2 sigma (.exceptional j)
        (SurfaceTarget.blowupTwo.effective.energy sigma))} = 0 := by
  dsimp only
  apply row_source_nonprimary_coefficient_eq_zero
  · exact fun gamma n ↦ SurfaceFirstDescendant.query_ne_points _ gamma _ _ n
  · rfl

end AxiomaticGWTest.SurfaceGenusTwoBlowupNCoefficients
