/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.Components
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.IncidenceSquares

/-! # Termwise incidence vanishing for forbidden doubled exceptional interior squares -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveSquare
open BlowupTwoExceptionalIncidence (Allowed data doubleCap)
open BlowupTwoMixedExceptionalInteriorPairs.FaceSquares (vertexZero vertexZero_sound)
open BlowupTwoDoubleExceptionalDivisor (beta)

/-- Recognize zeros of the original vertex, including lower-genus incidence on the doubled axes. -/
def impossible (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (d : S → ℕ)
    (l : DecidableEq S) (b : X.Curve) (a : S → SurfaceBasisLabel X) : Bool :=
  vertexZero (ancestorValue low) g S h d l b a ||
    decide (g ≤ 1 ∧ (∀ t : Fin 3, b t ≤ doubleCap t) ∧
      ¬Allowed b (data (SurfaceAncestorKey.ofLabels g S h b d a).primaryLabels))

private theorem impossible_sound (c : CertifiedComponents X)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (d : S → ℕ)
    (l : DecidableEq S) (b : X.Curve) (a : S → SurfaceBasisLabel X)
    (hz : impossible g S h d l b a = true) : c.vertex (ancestorValue low) g S h b d a = 0 := by
  rw [impossible, Bool.or_eq_true, decide_eq_true_eq] at hz
  rcases hz with hz | ⟨hg, hb, ha⟩
  · exact vertexZero_sound c _ g S h d l b a hz
  · let q := SurfaceAncestorKey.ofLabels g S h b d a
    unfold CertifiedComponents.vertex
    by_cases hd : q.DimensionCompatible
    · simp only [show SurfaceAncestorKey.ofLabels g S h b d a = q from rfl, if_pos hd, if_pos hg]
      rw [c.sound, SurfaceLowGenusPointCache.pointCoordinateComponent,
        SurfaceLowGenusPointCache.coordinateComponent_eq]
      exact BlowupTwoExceptionalIncidence.component_zero_of_le_doubleCap q hb ha
    · simp only [show SurfaceAncestorKey.ofLabels g S h b d a = q from rfl, if_neg hd]

/-- These twelve full-class keys contain a hyperplane or the other exceptional divisor. -/
def forbidden : Fin 12 → Fin 16 := ![0,1,2,3,4,6,8,9,10,11,12,14]

/-- Every class and node assignment of the indicated one of eleven original graph sources. -/
def checkForbidden (i : Fin 2) (j : Fin 12) (g : Fin 11) : Bool :=
  pulledSquareZero impossible 1 (beta i) (powers i (forbidden j)) (labels i (forbidden j)) g

set_option maxRecDepth 65536
set_option maxHeartbeats 12000000 in
-- The full coordinate splittings and all paired node labels occur in every support test.
/-- Every assignment in all 264 forbidden signed graphs has a certified zero vertex. -/
theorem forbidden_support (i : Fin 2) (j : Fin 12) (g : Fin 11) :
    checkForbidden i j g = true := by
  fin_cases i <;> fin_cases j <;> fin_cases g <;> decide +kernel

/-- Each individual signed contribution vanishes before adding the eleven graph sources. -/
theorem forbidden_parts (c : CertifiedComponents X) (i : Fin 2) (j : Fin 12) (g : Fin 11) :
    squarePart c i (forbidden j) g = 0 :=
  pulledSquarePart_eq_zero_of_support impossible _ (impossible_sound c) _ _ _ _ g
    (forbidden_support i j g)

/-- The complete ancestor on a square containing a hyperplane or the foreign divisor vanishes. -/
theorem forbidden_values (i : Fin 2) (j : Fin 12) :
    ancestorValue low (squareKey i (forbidden j)) = 0 := by
  rw [square_sum initial]
  simp only [forbidden_parts, Finset.sum_const_zero]

end AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
