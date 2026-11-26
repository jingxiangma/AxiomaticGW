/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLinePointPairs
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineIncidence

/-! # Products of two first cotangent classes with a point on the double strict line -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLinePointPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare
open BlowupTwoDoubleLine (curve)
open BlowupTwoDoubleLineIncidence (vertexZero vertexZero_sound)
open GluingExpression
open BlowupTwoDoubleLineComponents.Third (backend)

/-- The three divisors paired with the first point descendant. -/
def productIndex (i : Fin 3) : Fin 8 := Fin.natAdd 5 i

/-- Both markings in the order used by the two-marked product relation. -/
def productLabels (i : Fin 3) : Fin 2 → SurfaceBasisLabel X := ![(first (productIndex i)).label,
  .point]

private theorem product_sum (i : Fin 3) : ancestorValue low (fullKey (productIndex i)) =
    ∑ g, productGraph (backend.vertex low) curve (productLabels i) g := by
  rw [backend.vertex_eq, component_eq, vertex_eq]
  fin_cases i
  all_goals
    exact ancestorValue_twoMarking_product low _ rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ (by decide +kernel) (by decide +kernel)

/-- The actual decorated boundary source, with the producer's original flag decisions. -/
def productTerm (g : Fin 25) : CotangentTerm 2 (Fin 2) :=
  ⟨(GenusTwoPsiProduct.boundaryTerm g).1, (GenusTwoPsiProduct.boundaryTerm g).2,
    GenusTwoPsiProduct.boundaryLabelDecisions g⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
-- Exhaust all splittings and dual labelings in the 25 original graphs.
private theorem product_support (i : Fin 3) (g : Fin 25) :
    externalZero (vertexZero low) (productTerm g) curve 0 (productLabels i) = true := by
  fin_cases i <;> fin_cases g <;> decide +kernel

/-- All weighted contributions vanish with the actual reconstructed genus-two low-power values. -/
theorem product_zero (i : Fin 3) (g : Fin 25) :
    productGraph (backend.vertex low) curve (productLabels i) g = 0 := by
  unfold productGraph
  apply mul_eq_zero_of_right
  change (productTerm g).expression.surfaceDecoratedEval X _ (productTerm g).decoration
    curve 0 (productLabels i) = 0
  rw [← externalScalar_eq]
  exact zeroPointContraction_of_support (vertexZero low) _ (vertexZero_sound backend low) _ _ _ _ _
    (product_support i g)

/-- The mixed descendant, in both marking orders, for every first divisor/point product. -/
theorem product_accepted (i : Fin 3) (last : Bool) :
    SurfaceGenusTwoBlowupDescendants.queryValue? 0 (request (productIndex i) last) = some 0 := by
  rw [query_from_ancestor, product_sum]
  simp only [product_zero, Finset.sum_const_zero]

end AxiomaticGW.BlowupTwoDoubleLinePointPairs
