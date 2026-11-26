/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleLineMarkedReplay
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLinePointSquares
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLinePointProducts

/-! # Native field comparison for the sixteen original interior point descendants on 2L -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoDoubleLinePairs
open SurfaceGenusTwoBlowupDescendants EquivariantCoefficients
open AxiomaticGW.BlowupTwoDoubleLinePointPairs (request squareIndex productIndex)

/-- Row of the positive-plane pair report for each square or product in either marking order. -/
def pointIndex (j : Fin 8) (last : Bool) : Fin 100 :=
  if last then ![23, 24, 44, 64, 84, 43, 63, 83] j else ![86, 85, 89, 92, 95, 90, 93, 96] j

private theorem point_binding : ∀ (j : Fin 8) (last : Bool),
    (requests (pointIndex j last), values (pointIndex j last)) = (request j last, 0) := by
  decide +kernel

/-- The original Bl₂ mixed evaluator and the literal native fraction both vanish. -/
theorem point_certified (j : Fin 8) (last : Bool) :
    let i := pointIndex j last
    queryValue? 0 (requests i) = some (values i) ∧ equivariant i = (values i : Coefficient) ∧
      Specializes (equivariant i) (values i) := by
  refine ⟨?_, BlowupTwoPositivePlaneEnergyTwoPairs.equivariant_eq_ordinary _,
    BlowupTwoPositivePlaneEnergyTwoPairs.specializes _⟩
  apply (congrArg (fun p ↦ queryValue? 0 p.1 = some p.2) (point_binding j last)).mpr
  exact Fin.addCases (m := 5) (n := 3)
    (fun k ↦ BlowupTwoDoubleLinePointPairs.square_accepted k last)
    (fun k ↦ BlowupTwoDoubleLinePointPairs.product_accepted k last) j

/-- Adding the sixteen interior point rows to the fifty marked reductions gives 66 distinct rows. -/
theorem card_marked_and_point :
    (markedRows ∪ Finset.univ.image
      (fun p : Fin 8 × Bool ↦ pointIndex p.1 p.2)).card = 66 := by decide +kernel

end AxiomaticGW.GKM.BlowupTwoDoubleLinePairs
