import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleLinePointPairReplay

/-! # Marked reconstruction and signed localization controls on 2L -/

namespace AxiomaticGWTest.GKM.BlowupTwoDoubleLinePairs
open AxiomaticGW AxiomaticGW.GKM SurfaceGenusTwoBlowupDescendants EquivariantCoefficients
open AxiomaticGW.GKM.BlowupTwoDoubleLinePairs

/-- In the primary H equation both the class pairing and the cup correction contribute. -/
theorem primary_H : CheckedDescendant 0
    (⟨2, ![0, 0, 2], [⟨.unit, 4⟩, ⟨.hyperplane, 0⟩]⟩ : SurfaceQuery .blowupTwo) (-1/384) := by
  exact (marked_certified (j := 10) (by decide +kernel)).1

/-- The interior unit/H square has a negative signed F₁ comparison and falls outside the
singleton marking reductions. -/
theorem signed_square :
    (8 : Fin 100) ∉ markedRows ∧ values 8 = -3/80 ∧
      F1DoubleExceptionalPairs.values (sourceRow 8) = 3/80 ∧
      equivariant 8 =
        -StrictLineCoverTransport.field (F1DoubleExceptionalPairs.equivariant (sourceRow 8)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  rw [field_comparison, show sign (requests 8) = -1 by decide +kernel, Rat.cast_neg,
    Rat.cast_one, neg_one_mul]

/-- The H/point product is an original mixed descendant at 2L in either order. -/
theorem point_product (last : Bool) :
    queryValue? 0 (if last then ⟨2, ![0, 0, 2], [⟨.hyperplane, 1⟩, ⟨.point, 1⟩]⟩ else
      (⟨2, ![0, 0, 2], [⟨.point, 1⟩, ⟨.hyperplane, 1⟩]⟩ : SurfaceQuery .blowupTwo)) = some 0 := by
  cases last
  · exact (point_certified 5 false).1
  · exact (point_certified 5 true).1

end AxiomaticGWTest.GKM.BlowupTwoDoubleLinePairs
