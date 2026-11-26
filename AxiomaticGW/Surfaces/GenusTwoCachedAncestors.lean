/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCachedTerms
public import AxiomaticGW.Surfaces.GenusTwoAncestors

/-!
# Reusing certified components in genus-two ancestor equations

Each stored component expression is proved equal to the original residual
algorithm before it is used in a boundary contraction. The existing cache
retains the original algorithm at every unlisted key. Consequently neither
complete cache coverage nor an additional numerical seed is required.

The cached square and product equations preserve the entire uncollected
expression, including all curve splittings, node powers and repeated terms.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo

/-- Assemble individually checked component expressions without evaluating
their original recursive algorithms again at every graph occurrence. -/
def ResidualCache.ofEntries {X : SurfaceTarget} {n : ℕ}
    (keys : Fin n → SurfaceAncestorKey X)
    (entries : Fin n → RationalTerms (SurfaceAncestorKey X))
    (hinj : Function.Injective keys)
    (hentries : ∀ i, entries i = residualTerms (keys i)) : ResidualCache X where
  queries := Finset.univ.image keys
  values := Finset.univ.val.map (fun i ↦ (keys i, entries i))
  values_eq := by
    rw [Finset.image_val_of_injOn (fun i _ j _ h ↦ hinj h), Multiset.map_map]
    apply Multiset.map_congr rfl
    intro i _
    exact congrArg (fun x ↦ (keys i, x)) (hentries i)

/-- The complete signed boundary with certified terminal components. -/
def boundaryReductionTermsCached {X : SurfaceTarget} {S : Type} [Fintype S]
    (cache : ResidualCache X) (b : CotangentCombination 2 S) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) : RationalTerms (SurfaceAncestorKey X) :=
  b.bind fun t ↦ RationalTerms.scale (-t.1)
    (t.2.expression.surfaceDecoratedTerms X (cachedVertexTerms X cache)
      t.2.decoration beta k a)

/-- Every term and coefficient agrees before any collection or cancellation. -/
theorem boundaryReductionTermsCached_eq {X : SurfaceTarget} {S : Type} [Fintype S]
    (cache : ResidualCache X) (b : CotangentCombination 2 S) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    boundaryReductionTermsCached cache b beta k a = boundaryReductionTerms X b beta k a := by
  rw [boundaryReductionTermsCached, cachedVertexTerms_eq]
  rfl

/-- Use the original square/product selection and exact marking frames. -/
def ancestorReductionTermsCached {X : SurfaceTarget} (cache : ResidualCache X)
    (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi) :
    RationalTerms (SurfaceAncestorKey X) :=
  if hs : (squareMarks q).Nonempty then
    boundaryReductionTermsCached cache (GenusTwoPsiSquare.boundaryRemainder
      (q.orderedInsertions.length - 1)) q.beta (squareLowerPowers q hs)
        (q.orderedLabels ∘ squareFrame q hs)
  else
    boundaryReductionTermsCached cache (GenusTwoPsiProduct.boundaryRemainder
      (q.orderedInsertions.length - 2)) q.beta (productLowerPowers q hk hs)
        (q.orderedLabels ∘ productFrame q hk hs)

/-- A partial certified component cache preserves the original ancestor equation. -/
theorem ancestorReductionTermsCached_eq {X : SurfaceTarget} (cache : ResidualCache X)
    (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi) :
    ancestorReductionTermsCached cache q hk = ancestorReductionTerms q hk := by
  unfold ancestorReductionTermsCached ancestorReductionTerms
  split_ifs <;> exact boundaryReductionTermsCached_eq cache _ _ _ _

end AxiomaticGW.SurfaceGenusTwo
