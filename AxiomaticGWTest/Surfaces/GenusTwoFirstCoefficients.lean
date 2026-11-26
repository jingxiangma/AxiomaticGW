/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoFirstCoefficients

@[expose] public section

namespace AxiomaticGWTest.Surfaces.GenusTwoFirstCoefficients
open AxiomaticGW SurfaceGenusTwo SurfacePolynomialReduction

-- Equal energy does not identify the two exceptional curve classes on Bl₂P².
theorem equal_energy_different_class :
    firstCoefficientVertex .blowupTwo ![1, 0, 0] .hyperplane 1
      2 (Fin 2) (by unfold StableArity; omega) ![0, 1, 0]
      ![1, 0] ![.hyperplane, .point] = 0 := by
  decide +kernel

-- A requested first descendant has no coefficient in a smaller-class primary tail.
theorem smaller_class_descendant_coefficient :
    RationalTerms.coefficient (normalizedTerms
      (SurfaceAncestorKey.ofLabels 2 (Fin 4) (by unfold StableArity; omega)
        (![1, 1] : SurfaceTarget.hirzebruchOne.Curve)
        ![1, 0, 0, 0] ![.exceptional 0, .point, .point, .point]))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![0, 1] .hyperplane 2)} = 0 := by
  rw [coefficient_normalizedTerms_eq_direct_of_not_points _ rfl _
    (fun beta n ↦ SurfaceFirstDescendant.query_ne_points ![0, 1] beta .hyperplane 2 n)]
  exact coefficient_directNormalizedTerms_eq_zero _ le_rfl _ (by decide)

-- The full calibration tail remains: its smaller-class primary coefficient is one.
theorem smaller_class_primary_calibration_coefficient :
    RationalTerms.coefficient (normalizedTerms
      (SurfaceAncestorKey.ofLabels 2 (Fin 4) (by unfold StableArity; omega)
        (![1, 1] : SurfaceTarget.hirzebruchOne.Curve)
        ![1, 0, 0, 0] ![.exceptional 0, .point, .point, .point]))
      {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![0, 1] 3)} = 1 := by
  decide +kernel

-- Dimension-incompatible first-descendant requests cannot acquire a terminal value.
theorem dimension_incompatible_terminal :
    firstCoefficientVertex .hirzebruchOne 0 .point 0
      2 (Fin 1) (by unfold StableArity; omega) 0 ![1] ![.point] = 0 := by
  decide +kernel

-- A nonzero terminal is retained at the precise full query and class.
theorem matching_terminal :
    firstCoefficientVertex .hirzebruchOne ![0, 1] .hyperplane 2
      2 (Fin 3) (by unfold StableArity; omega) ![0, 1]
      ![1, 0, 0] ![.hyperplane, .point, .point] = 1 := by
  decide +kernel

-- Every positive remainder is excluded on the one-psi main component, uniformly
-- in the number of points and every target, without excluding rational complements.
theorem onePsi_positive_remainder {X : SurfaceTarget} (beta : X.Curve)
    (b : SurfaceBasisLabel X) (m n : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity 2 S) (s : S) (delta : X.Curve) (hd : delta ≠ 0)
    (a : S → SurfaceBasisLabel X) :
    let v : Variable X := .inr (SurfaceFirstDescendant.query 2 beta b m)
    remainderVertex X v (coefficientVertex X v) n 2 S h
      (Pi.single s 1) inferInstance delta a = 0 := by
  dsimp only
  rw [remainderVertex_onePsi_of_not_points _
    (fun gamma k ↦ SurfaceFirstDescendant.query_ne_points beta gamma b m k), if_neg hd]

end AxiomaticGWTest.Surfaces.GenusTwoFirstCoefficients
