/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoTerms

/-!
# Reusing reconstructed component values in genus-two equations

A graph equation may repeat the same low-genus component thousands of times.
Precompute the existing residual expression at a finite set of component
queries, then reuse those expressions during contraction. Missing queries
fall back to the original algorithm, so no completeness assumption or supplied
numerical table is needed. The resulting vertex function is equal to the
original one, including every coefficient and uncollected monomial.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo

/-- Stored component expressions with their exact specification. The equality field
prevents imported or duplicated entries from changing the reconstructed values. -/
structure ResidualCache (X : SurfaceTarget) where
  /-- Component queries selected for reuse. -/
  queries : Finset (SurfaceAncestorKey X)
  /-- Each selected query and its original residual expression, stored once. -/
  values : Multiset (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X))
  /-- Stored expressions are exactly those computed by the original algorithm. -/
  values_eq : values = queries.val.map (fun q ↦ (q, residualTerms q))

/-- Materialize the cache as data before passing the vertex function to contraction. -/
def ResidualCache.ofQueries (X : SurfaceTarget) (queries : Finset (SurfaceAncestorKey X)) :
    ResidualCache X :=
  ⟨queries, queries.val.map (fun q ↦ (q, residualTerms q)), rfl⟩

/-- Reuse stored expressions and compute a missing query with the original algorithm. -/
def cachedVertexTerms (X : SurfaceTarget) (cache : ResidualCache X) :
    SurfaceVertexValues X (RationalTerms (SurfaceAncestorKey X)) :=
  fun g S _ h beta k a ↦
    let q := SurfaceAncestorKey.ofLabels g S h beta k a
    if q ∈ cache.queries then
      (cache.values.map fun t ↦ if t.1 = q then t.2 else 0).sum
    else residualTerms q

/-- Any finite cache, including an empty or incomplete one, preserves the algorithm. -/
theorem cachedVertexTerms_eq (X : SurfaceTarget) (cache : ResidualCache X) :
    cachedVertexTerms X cache = vertexTerms X := by
  funext g S inst h beta k a
  simp only [cachedVertexTerms, vertexTerms, cache.values_eq, Multiset.map_map, Function.comp_def,
    ← Finset.sum_eq_multiset_sum, Finset.sum_ite_eq']
  split_ifs <;> rfl

end AxiomaticGW.SurfaceGenusTwo
