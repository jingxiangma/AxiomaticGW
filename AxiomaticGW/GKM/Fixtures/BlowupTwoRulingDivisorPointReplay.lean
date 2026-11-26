/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoPositivePlaneEnergyTwoCoverage
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoRulingDivisorPoint

/-! # Native comparison for the two ruling divisor–point interior shapes -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoPositivePlaneEnergyTwoPairs
open SurfaceGenusTwoBlowupDescendants EquivariantCoefficients

/-- Each index is in the full 300-row native pair frame. The two orientations use separate rows. -/
def rulingDivisorPointIndex (i : Fin 2) (j : Fin 3) (square pointFirst : Bool) : Fin 300 :=
  match square, pointFirst with
  | false, false => ![![243,263,283], ![143,183,163]] i j
  | false, true => ![![290,293,296], ![190,196,193]] i j
  | true, false => ![![244,264,284], ![144,184,164]] i j
  | true, true => ![![289,292,295], ![189,195,192]] i j

private theorem ruling_binding : ∀ (i : Fin 2) (j : Fin 3) (square pointFirst : Bool),
    let n := rulingDivisorPointIndex i j square pointFirst
    (requests n, values n) = (BlowupTwoRulingDivisorPoint.request i j square pointFirst,
      BlowupTwoRulingDivisorPoint.value j square) := by decide +kernel

/-- All 24 rows have the original mixed descendant proof and a matching exact field value. -/
theorem ruling_divisor_point_certified (i : Fin 2) (j : Fin 3) (square pointFirst : Bool) :
    let n := rulingDivisorPointIndex i j square pointFirst
    CheckedDescendant 0 (requests n) (values n) ∧ equivariant n = (values n : Coefficient) ∧
      Specializes (equivariant n) (values n) := by
  refine ⟨?_, equivariant_eq_ordinary _, specializes _⟩
  apply (congrArg (fun p ↦ CheckedDescendant 0 p.1 p.2) (ruling_binding i j square pointFirst)).mpr
  exact BlowupTwoRulingDivisorPoint.checked i j square pointFirst

/-- The native index set of the divisor–point squares and products. -/
def rulingDivisorPoints : Finset (Fin 300) :=
  Finset.univ.image fun t : Fin 2 × Fin 3 × Bool × Bool ↦
    rulingDivisorPointIndex t.1 t.2.1 t.2.2.1 t.2.2.2

/-- The new interior rows are disjoint from the marked equations and the 2L point rows. -/
theorem ruling_divisor_point_counts : rulingDivisorPoints.card = 24 ∧
    Disjoint rulingDivisorPoints verifiedRows ∧
    (verifiedRows ∪ rulingDivisorPoints).card = 190 := by decide +kernel

/-- Index lookup for the command-line query, retaining both curve coordinates and marking order. -/
theorem ruling_divisor_point_accepted {n : Fin 300} (h : n ∈ rulingDivisorPoints) :
    CheckedDescendant 0 (requests n) (values n) := by
  obtain ⟨⟨i,j,s,p⟩, _, rfl⟩ := Finset.mem_image.mp h
  exact (ruling_divisor_point_certified i j s p).1

end AxiomaticGW.GKM.BlowupTwoPositivePlaneEnergyTwoPairs
