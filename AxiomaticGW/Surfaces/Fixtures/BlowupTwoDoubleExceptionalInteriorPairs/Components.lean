/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.Frame

/-! # Lower-genus components with the proven exceptional incidence restriction -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache
open BlowupTwoExceptionalIncidence (Allowed data doubleCap component_zero_of_le_doubleCap)

/-- Omit precisely the forbidden vertex profiles in the doubled exceptional coordinate box. -/
def withIncidence (c : CertifiedComponents X) : CertifiedComponents X where
  value q := if (∀ j : Fin 3, q.beta j ≤ doubleCap j) ∧ ¬Allowed q.beta (data q.primaryLabels)
    then 0 else c.value q
  sound q := by
    split_ifs with h
    · rw [pointCoordinateComponent, coordinateComponent_eq]
      exact (component_zero_of_le_doubleCap q h.1 h.2).symm
    · exact c.sound q

/-- The complete previously checked lower-genus singleton vertices, with incidence pruning. -/
def initial : CertifiedComponents X :=
  withIncidence BlowupTwoDoubleExceptionalComponents.ThirdPower.backend

/-- Replay one exact cotangent-degree layer. An absent key uses the preceding certified
recursion step, and an inadmissible exceptional profile uses its proven incidence zero. -/
def componentLayer (c : CertifiedComponents X) (power : ℕ) (entries : List (Entry X)) :
    CertifiedComponents X := withIncidence {
  value q := if q.totalPsi = power then stageLookup (stagedValue c.value) q entries else c.value q
  sound q := by
    split
    · exact stageLookup_eq (stagedValue c.value) (stagedValue_eq c.sound) q entries
    · exact c.sound q }

namespace MarkedVertex

/-- A stable marked key for a rational or elliptic component in the exceptional face. -/
def node (g : ℕ) (c : X.Curve) (m : List (SurfaceInsertion X))
    (h : 3 ≤ 2 * g + m.length := by simp only [List.length_cons, List.length_nil]; omega) :
    SurfaceAncestorKey X := GenusTwoSecondUnitPairs.TwoBlowupComponents.componentKey g c m h

/-- Unit insertion of the indicated power. -/
abbrev unit (p : ℕ) : SurfaceInsertion X := ⟨.unit, p⟩
/-- Hyperplane insertion of the indicated power. -/
abbrev hyperplane (p : ℕ) : SurfaceInsertion X := ⟨.hyperplane, p⟩
/-- Exceptional divisor at the indicated axis and power. -/
abbrev divisor (i : Fin 2) (p : ℕ) : SurfaceInsertion X := ⟨.exceptional i, p⟩
/-- Point insertion of the indicated power. -/
abbrev point (p : ℕ) : SurfaceInsertion X := ⟨.point, p⟩

end MarkedVertex

end AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
