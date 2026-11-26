/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.CertifiedComponentLayers
public import AxiomaticGW.Surfaces.GenusTwoOneMarkingSquare
public import AxiomaticGW.Surfaces.GenusTwoOneMarkingTransfer

/-! # Leading genus-two ancestor squares in twice the strict line of Bl₂

At one marking, even the point state has cotangent power two in virtual dimension.
The genus-two cotangent-square relation evaluates its leading term entirely in lower genus.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLine
open SurfaceGenusTwo SurfaceGenusTwoPositiveSquare GenusTwoPsiSquare
open SurfaceDescendant SurfaceGenusTwoBlowupDescendants

/-- The full class `2(H − E₁ − E₂)` in the two-exceptional and strict-line basis. -/
def curve : SurfaceTarget.blowupTwo.Curve := ![0,0,2]

/-- An original signed-graph contraction with a globally certified lower-genus backend. -/
def graph (c : CertifiedComponents .blowupTwo) (a : SurfaceBasisLabel .blowupTwo)
    (k : ℕ) (j : Fin 10) : ℚ :=
  (boundaryTerm j).1.surfaceDecoratedEval .blowupTwo (c.vertex (fun _ ↦ 0))
    (boundaryTerm j).2 curve (fun _ ↦ k) (fun _ ↦ a)

/-- Every high singleton uses only ten lower-genus graphs, for every genus-two base. -/
theorem ancestor_eq_sum (c : CertifiedComponents .blowupTwo)
    (base : SurfaceAncestorKey .blowupTwo → ℚ) (a : SurfaceBasisLabel .blowupTwo) (k : ℕ) :
    ancestorValue base (oneMarkingKey curve a (k + 2)) =
      ∑ j, GenusTwoPsiSquare.boundary (boundaryIndex j) * graph c a k j := by
  have hv : c.vertex (fun _ ↦ 0) = constantVertex .blowupTwo := by
    rw [CertifiedComponents.vertex_eq, component_eq, SurfaceGenusTwoPositiveDivisorPairs.vertex_eq]
    funext g S inst h b d a
    exact eval_zero_vertexTerms .blowupTwo g S h b d a
  rw [ancestorValue_oneMarking_square, oneMarkingSquareValue, ← hv]
  rfl

set_option maxRecDepth 65536

/-- A point marking annihilates each complete original graph source at the full double line. -/
theorem point_graphs (j : Fin 10) :
    graph (CertifiedComponents.bounded .blowupTwo) .point 0 j = 0 := by
  fin_cases j <;> decide +kernel

/-- The point ancestor is zero independently of every genus-two canonical family. -/
theorem point_ancestor (base : SurfaceAncestorKey .blowupTwo → ℚ) :
    ancestorValue base (oneMarkingKey curve .point 2) = 0 := by
  rw [show 2 = 0 + 2 by rfl, ancestor_eq_sum (CertifiedComponents.bounded .blowupTwo)]
  simp only [point_graphs, mul_zero, Finset.sum_const_zero]

/-- The actual stable-map point descendant, with its exact original calibration. -/
theorem point_accepted :
    queryValue? 0 (⟨2, curve, [⟨.point, 2⟩]⟩ : SurfaceQuery .blowupTwo) = some 0 := by
  let actual := SurfaceGenusTwoBlowupRecursion.values (X := .blowupTwo) 0
  rw [← queryValueWith?_eq_of_table 0 2 actual (fun _ _ ↦ rfl) _ (by decide +kernel),
    queryValueWith?_oneMarking]
  rw [show oneMarkingTerms (reconstructedCalibrationMatrix .blowupTwo) curve .point 2 0 =
    RationalTerms.term 1 {oneMarkingKey curve .point 2} by decide +kernel]
  simp only [RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton, map_one,
    one_mul, ancestorValueWith, point_ancestor]

end AxiomaticGW.BlowupTwoDoubleLine
