/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalSingletons.ThirdPower
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.IncidenceVertices

/-! # Unit, hyperplane and foreign-divisor squares on the doubled exceptional axes -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalSingletons
open SurfaceGenusTwo GenusTwoPsiSquare
open BlowupTwoDoubleExceptionalDivisor (beta squareGraph ancestor_eq_sum)
open BlowupTwoDoubleExceptionalComponents.ThirdPower (backend)

private def stagedGraph (i : Fin 2) (a : SurfaceBasisLabel .blowupTwo) (k : ℕ) (j : Fin 10) : ℚ :=
  (boundaryTerm j).1.surfaceDecoratedEval .blowupTwo (backend.vertex (fun _ ↦ 0))
    (boundaryTerm j).2 (beta i) (fun _ ↦ k) (fun _ ↦ a)

private theorem stagedGraph_eq (i : Fin 2) (a : SurfaceBasisLabel .blowupTwo) (k : ℕ) (j : Fin 10) :
    stagedGraph i a k j = squareGraph i a k j := by
  simp only [stagedGraph, squareGraph, SurfaceGenusTwoPositiveSquare.CertifiedComponents.vertex_eq]

/-- The hyperplane and the exceptional divisor different from the supporting curve. -/
def disjointDivisor (i : Fin 2) (foreign : Bool) : SurfaceBasisLabel .blowupTwo :=
  if foreign then .exceptional i.rev else .hyperplane

private def unitRows : Fin 10 → ℚ :=
  ![0, 0, 0, -1/576, -1/12, -1/24, 0, -1/24, 0, -1]

set_option Elab.async false
set_option maxRecDepth 65536

private theorem vertex_incidence (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (b : SurfaceTarget.blowupTwo.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel .blowupTwo)
    (hb : b ≤ BlowupTwoExceptionalIncidence.doubleCap)
    (hz : ¬BlowupTwoExceptionalIncidence.Allowed b (BlowupTwoExceptionalIncidence.profile a)) :
    backend.vertex (fun _ ↦ 0) g S h b k a = 0 := by
  let q := SurfaceAncestorKey.ofLabels g S h b k a
  unfold SurfaceGenusTwoPositiveSquare.CertifiedComponents.vertex
  by_cases hd : q.DimensionCompatible
  · by_cases hg : g ≤ 1
    · simp only [show SurfaceAncestorKey.ofLabels g S h b k a = q from rfl, if_pos hd, if_pos hg]
      rw [backend.sound, SurfaceLowGenusPointCache.pointCoordinateComponent,
        SurfaceLowGenusPointCache.coordinateComponent_eq]
      apply BlowupTwoExceptionalIncidence.component_zero_of_le_doubleCap q hb
      exact (BlowupTwoExceptionalIncidence.profile_ofLabels g S h b k a).symm ▸ hz
    · simp only [show SurfaceAncestorKey.ofLabels g S h b k a = q from rfl, if_pos hd, if_neg hg]
  · simp only [show SurfaceAncestorKey.ofLabels g S h b k a = q from rfl, if_neg hd]

private theorem divisor_graphs (i : Fin 2) (foreign : Bool) (j : Fin 10) :
    squareGraph i (disjointDivisor i foreign) 1 j = 0 := by
  rw [← stagedGraph_eq]
  apply BlowupTwoExceptionalIncidence.decorated_graph_zero _ vertex_incidence
  · intro l
    fin_cases i <;> fin_cases l <;> decide +kernel
  · fin_cases i <;> cases foreign <;> decide +kernel

/-- Each of the disjoint divisor ancestors vanishes at its dimension-compatible power. -/
theorem divisor_ancestor (base : SurfaceAncestorKey .blowupTwo → ℚ) (i : Fin 2) (foreign : Bool) :
    ancestorValue base (oneMarkingKey (beta i) (disjointDivisor i foreign) 3) = 0 := by
  rw [show 3 = 1 + 2 by rfl, ancestor_eq_sum]
  simp only [divisor_graphs, mul_zero, Finset.sum_const_zero]

set_option maxHeartbeats 8000000 in
-- Two retained powers at the external marking require lower-genus descendant contractions.
private theorem unit_graphs (i : Fin 2) (j : Fin 10) :
    squareGraph i .unit 2 j = unitRows j := by
  rw [← stagedGraph_eq]
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- The unit ancestor before converting the marking from ancestor to stable-map cotangent class. -/
theorem unit_ancestor (base : SurfaceAncestorKey .blowupTwo → ℚ) (i : Fin 2) :
    ancestorValue base (oneMarkingKey (beta i) .unit 4) = -1/1152 := by
  rw [show 4 = 2 + 2 by rfl, ancestor_eq_sum]
  simp only [unit_graphs]
  decide +kernel

end AxiomaticGW.BlowupTwoDoubleExceptionalSingletons
