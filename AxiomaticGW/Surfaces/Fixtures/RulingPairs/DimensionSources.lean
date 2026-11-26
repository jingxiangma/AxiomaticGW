/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.DecoratedPointDimension
public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.FullSquareSources

/-! # Dimension-pruned ruling contractions on the complete mixed boundary source -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingInterior.FullSquares
open SurfaceGenusTwo SurfaceGenusTwoPositiveSquare GluingExpression
open BlowupTwoRuling (X)

/-- Every certified genus-two mixed component discards keys outside the virtual dimension. -/
theorem component_graded (c : CertifiedComponents X) (next : SurfaceAncestorKey X → ℚ) :
    GradedVertex (c.vertex next) := by
  intro g S _ h beta k a hd
  have hq := (SurfaceLowGenusPointCache.virtualDefect_ofLabels g S h beta k a).not.mpr hd
  simp only [CertifiedComponents.vertex, if_neg hq]

/-- The optimized decorated graph contracts exactly the exterior-power integrand in the source. -/
def dimensionExternal (v : SurfaceVertexValues X ℚ) {g : ℕ} {S : Type} [Fintype S]
    (z : CotangentTerm g S) (b : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) : ℚ :=
  z.expression.dimensionPointContraction X (SurfacePointPullback.vertex X v)
    (z.expression.withExternalPowers z.decoration k) z.labels b 0 a

/-- The pruning step preserves this original source exactly. -/
theorem dimensionExternal_eq (v : SurfaceVertexValues X ℚ) (hv : GradedVertex v)
    {g : ℕ} {S : Type} [Fintype S] (z : CotangentTerm g S) (b : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    dimensionExternal v z b k a = externalScalar X v z b k a := by
  rw [dimensionExternal, dimensionPointContraction_eq (pointPullback_dimension hv),
    scalarPointContraction_eq, externalScalar,
    ← zeroPointContraction_eq X (SurfacePointPullback.vertex X v)]
  rw [SurfacePointPullback.vertex]

/-- Prune the exact eleven signed cotangent sources at each internal splitting. -/
def dimensionPart (i : Fin 2) (r : Fin 21) (g : Fin 11) : ℚ :=
  let q := key i r
  let h := has_square i r
  let n := q.orderedInsertions.length - 1
  let v := (BlowupTwoRuling.Third.backend i).vertex (BlowupTwoRuling.SingletonVertices.next i)
  let atGraph (z : CotangentTerm 2 (ExtraMarkings n (Fin 1))) :=
    dimensionExternal v z q.beta (squareLowerPowers q h) (q.orderedLabels ∘ squareFrame q h)
  Fin.cases (((fundamentalCorrections GenusTwoPsiSquare.stableArity (fun _ : Fin 1 ↦ 2) n).map
    fun t ↦ -(t.1 : ℚ) * atGraph t.2).sum)
    (fun j ↦ (((GenusTwoPsiSquare.boundaryCotangentTerm j).addMarkings n).map
      fun t ↦ -(-GenusTwoPsiSquare.boundary (GenusTwoPsiSquare.boundaryIndex j) * (t.1 : ℚ)) *
        atGraph t.2).sum) g

/-- The pruning step preserves this original source exactly. -/
theorem dimensionPart_eq (i : Fin 2) (r : Fin 21) (g : Fin 11) :
    dimensionPart i r g = part i r g := by
  simp only [part, pulledSquarePart, dimensionPart, dimensionExternal_eq _ (component_graded _ _)]

end AxiomaticGW.BlowupTwoRulingInterior.FullSquares
