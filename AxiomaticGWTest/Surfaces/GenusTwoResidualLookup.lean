/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoResidualLookup

/-! # Exact full-key lookup and fallback on a small class-zero cache -/

@[expose] public section
set_option maxRecDepth 20000

namespace AxiomaticGWTest.Surfaces.GenusTwoResidualLookup
open AxiomaticGW SurfaceGenusTwo

def key0 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0], ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩] :
    List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key12 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0], ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key18 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0], ([⟨.hyperplane, 0⟩] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key22 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0], ([⟨.exceptional 0, 0⟩] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def cache : ResidualCache .hirzebruchOne :=
  ResidualCache.ofQueries .hirzebruchOne {key0, key12, key18, key22}

def rational := SurfaceGenusZero.pointValue .hirzebruchOne
def elliptic := SurfaceGenusOne.pointValue .hirzebruchOne

/-- A genuine classical negative entry is retained by the executable first match. -/
theorem lookup_classical_negative :
    cache.lookup? key0 = some (RationalTerms.term (-1) 0) := by decide +kernel

/-- A stored zero is a hit, not an absent entry that needs recursive fallback. -/
theorem lookup_stored_zero : cache.lookup? key12 = some 0 := by decide +kernel

/-- Equal-genus, equal-class requests retain their different divisor states. -/
theorem lookup_distinct_divisor_states :
    cache.lookup? key18 = some (RationalTerms.term (-1 / 8) 0) ∧
    cache.lookup? key22 = some (RationalTerms.term (-1 / 24) 0) := by decide +kernel

/-- An unlisted complete curve class is not confused with any stored class-zero request. -/
theorem lookup_unlisted_full_class :
    cache.lookup?
      ⟨1, ![13, 0], ([⟨.hyperplane, 0⟩] : List (SurfaceInsertion .hirzebruchOne)),
        by decide⟩ = none := by decide +kernel

/-- Empty selections retain an explicit miss on every target and full query. -/
theorem empty_cache_lookup (X : SurfaceTarget) (q : SurfaceAncestorKey X) :
    (ResidualCache.ofQueries X ∅).lookup? q = none := by
  apply ResidualCache.lookup?_of_not_mem
  exact Finset.notMem_empty q

/-- The cached scalar evaluator reads the preserved negative classical coefficient. -/
theorem scalar_hit_sign :
    cachedLowerValueLookupWithPoints .hirzebruchOne cache rational elliptic key0 = -1 := by
  decide +kernel

/-- An actual miss evaluates the supplied backend rather than inventing a zero value. -/
theorem scalar_miss_uses_backend :
    cachedLowerValueLookupWithPoints .hirzebruchOne (ResidualCache.ofQueries .hirzebruchOne ∅)
      (fun _ ↦ 7) (fun _ ↦ 11)
      ⟨0, ![1, 0], ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩ = -7 := by decide +kernel

/-- The complete original equation remains available beyond the selected term and cache keys. -/
theorem complete_first_h_constant :
    L24Relation.pointConstantWithPointLookup .hirzebruchOne cache rational elliptic
      1 ![1, 1] ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] =
    L24Relation.pointConstant .hirzebruchOne 1 ![1, 1]
      ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] :=
  L24Relation.pointConstantWithPointLookup_eq _ _ _ _ rfl rfl _ _ _

end AxiomaticGWTest.Surfaces.GenusTwoResidualLookup
