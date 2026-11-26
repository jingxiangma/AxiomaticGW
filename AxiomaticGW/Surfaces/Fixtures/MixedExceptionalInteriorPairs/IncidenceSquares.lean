/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.IncidenceVertices
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.GraphSupport
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.SquareSources

/-! # Using exceptional incidence to prune all 308 signed square sources

The lower-genus support theorem recognizes zeros at any cotangent degree. A genus-two
vertex is consumed only at total power at most one, when the canonical terminal table applies.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveSquare

open SurfaceLowGenusPointCache
namespace FaceSquares
open BlowupTwoExceptionalIncidence (Allowed data cap component_zero)

/-- Test class and cohomology support on the exceptional face, independently of ψ degree. -/
def vertexZero (next : SurfaceAncestorKey X → ℚ) : SurfaceCotangentVertexValues X Bool :=
  fun g S _ h d _ beta a ↦
    let q := SurfaceAncestorKey.ofLabels g S h beta d a
    if q.DimensionCompatible then
      if g ≤ 1 then
        decide ((∀ i : Fin 3, beta i ≤ cap i) ∧ ¬Allowed beta (data q.primaryLabels))
      else decide (q.totalPsi ≤ 1) && (next q == 0)
    else true

theorem vertexZero_sound (c : CertifiedComponents X) (next : SurfaceAncestorKey X → ℚ)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (d : S → ℕ) (l : DecidableEq S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) :
    vertexZero next g S h d l beta a = true → c.vertex next g S h beta d a = 0 := by
  let q := SurfaceAncestorKey.ofLabels g S h beta d a
  unfold vertexZero CertifiedComponents.vertex
  by_cases hd : q.DimensionCompatible
  · by_cases hg : g ≤ 1
    · simp only [show (SurfaceAncestorKey.ofLabels g S h beta d a) = q from rfl, if_pos hd,
        if_pos hg, decide_eq_true_eq]
      intro hzero
      rw [c.sound, pointCoordinateComponent, coordinateComponent_eq]
      exact component_zero q hzero.1 hzero.2
    · simp only [show (SurfaceAncestorKey.ofLabels g S h beta d a) = q from rfl, if_pos hd,
        if_neg hg, Bool.and_eq_true]
      exact fun hz ↦ eq_of_beq hz.2
  · simp only [show (SurfaceAncestorKey.ofLabels g S h beta d a) = q from rfl,
      if_neg hd, implies_true]

def check (beta : X.Curve) (a b : SurfaceInsertion X) (i : Fin 11) : Bool :=
  pulledSquareZero (vertexZero (ancestorValue low)) 1 beta
    (Option.elim · b.psi (fun _ ↦ a.psi - 2)) (Option.elim · b.label (fun _ ↦ a.label)) i

theorem part_of_check (c : CertifiedComponents X) (j : Fin 28) (i : Fin 11)
    (h : check (squareBeta j) (oldMark j) (extraMark j) i = true) :
    squarePart c j i = 0 :=
  pulledSquarePart_eq_zero_of_support _ _ (vertexZero_sound c (ancestorValue low)) _ _ _ _ i h

end FaceSquares
end AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
