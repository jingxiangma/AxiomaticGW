/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsReplay
public import AxiomaticGW.Surfaces.GenusTwoResidualLookup
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.OfFn

/-!
# Selected certified components for the original F1 root term 122

This upward fixture keeps the 47 full keys observed in the frozen term-122
selector. Each key and signed value is bound to the already certified complete
722-entry table. Direct list storage avoids full-table indexing at lookup time.
Selection coverage is a performance hint; the existing ResidualCache contract
and exact fallback apply to every query. No contraction value is certified here.

The request is source (E,F)=(1,1), one added point and labels H,E0,E0,E0.
Index 122 belongs to the full original 815-term frame; the historical selector
visited its 721 nonzero-coefficient terms. Both frames remain unchanged.
Selector log SHA256: a5c4c41abad31443bffce2ffd25e3033c4746a82c1ef4ba144644d1e583a82f1
-/

@[expose] public section
set_option maxRecDepth 65536
set_option Elab.async false
set_option autoImplicit false

namespace AxiomaticGW.BlowupF1Root122Components
open SurfaceGenusTwo
abbrev X := SurfaceTarget.hirzebruchOne

/-- Proof-only binding to the original accepted full-table indices. -/
def globalIndex (i : Fin 47) : Fin 722 :=
  (![
    46, 169, 170, 182, 183, 260, 261, 281, 286, 393, 394, 397, 421, 422, 428, 429, 443, 458, 461, 464, 467, 471, 473, 486, 515, 523, 526, 527, 535, 538, 539, 561, 582, 590, 593, 631, 632, 638, 639, 648, 649, 653, 666, 668, 691, 700, 703
  ] : Fin 47 → Fin 722) i

/-- Named full-key constants; no full-table array lookup is used here. -/
def keyList : List (SurfaceAncestorKey X) :=
  [
    BlowupF1CompleteHComponents.key046,
    BlowupF1CompleteHComponents.key169,
    BlowupF1CompleteHComponents.key170,
    BlowupF1CompleteHComponents.key182,
    BlowupF1CompleteHComponents.key183,
    BlowupF1CompleteHComponents.key260,
    BlowupF1CompleteHComponents.key261,
    BlowupF1CompleteHComponents.key281,
    BlowupF1CompleteHComponents.key286,
    BlowupF1CompleteHComponents.key393,
    BlowupF1CompleteHComponents.key394,
    BlowupF1CompleteHComponents.key397,
    BlowupF1CompleteHComponents.key421,
    BlowupF1CompleteHComponents.key422,
    BlowupF1CompleteHComponents.key428,
    BlowupF1CompleteHComponents.key429,
    BlowupF1CompleteHComponents.key443,
    BlowupF1CompleteHComponents.key458,
    BlowupF1CompleteHComponents.key461,
    BlowupF1CompleteHComponents.key464,
    BlowupF1CompleteHComponents.key467,
    BlowupF1CompleteHComponents.key471,
    BlowupF1CompleteHComponents.key473,
    BlowupF1CompleteHComponents.key486,
    BlowupF1CompleteHComponents.key515,
    BlowupF1CompleteHComponents.key523,
    BlowupF1CompleteHComponents.key526,
    BlowupF1CompleteHComponents.key527,
    BlowupF1CompleteHComponents.key535,
    BlowupF1CompleteHComponents.key538,
    BlowupF1CompleteHComponents.key539,
    BlowupF1CompleteHComponents.key561,
    BlowupF1CompleteHComponents.key582,
    BlowupF1CompleteHComponents.key590,
    BlowupF1CompleteHComponents.key593,
    BlowupF1CompleteHComponents.key631,
    BlowupF1CompleteHComponents.key632,
    BlowupF1CompleteHComponents.key638,
    BlowupF1CompleteHComponents.key639,
    BlowupF1CompleteHComponents.key648,
    BlowupF1CompleteHComponents.key649,
    BlowupF1CompleteHComponents.key653,
    BlowupF1CompleteHComponents.key666,
    BlowupF1CompleteHComponents.key668,
    BlowupF1CompleteHComponents.key691,
    BlowupF1CompleteHComponents.key700,
    BlowupF1CompleteHComponents.key703
  ]

/-- Original exact signed values in the same selected order. -/
def valueList : List ℚ :=
  [
    (-1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ)
  ]

theorem keyList_length : keyList.length = 47 := rfl
theorem valueList_length : valueList.length = 47 := rfl

def key (i : Fin 47) : SurfaceAncestorKey X :=
  keyList[i.val]'(by simpa only [keyList_length] using i.isLt)

def value (i : Fin 47) : ℚ :=
  valueList[i.val]'(by simpa only [valueList_length] using i.isLt)

def entries (i : Fin 47) : RationalTerms (SurfaceAncestorKey X) :=
  RationalTerms.term (value i) 0

theorem globalIndex_injective : Function.Injective globalIndex := by decide +kernel

set_option maxHeartbeats 0 in
theorem key_eq_full (i : Fin 47) :
    key i = BlowupF1CompleteHComponents.key (globalIndex i) := by
  fin_cases i <;> rfl

set_option maxHeartbeats 0 in
theorem value_eq_full (i : Fin 47) :
    value i = BlowupF1CompleteHComponents.value (globalIndex i) := by
  fin_cases i <;> rfl

/-- Reuse the original full-key injectivity theorem. -/
theorem keys_injective : Function.Injective key := by
  intro i j h
  apply globalIndex_injective
  apply BlowupF1CompleteHComponents.keys_injective
  exact (key_eq_full i).symm.trans (h.trans (key_eq_full j))

/-- Reuse the accepted residual equations; no ancestor algorithm is recomputed. -/
theorem entries_eq (i : Fin 47) : entries i = residualTerms (key i) := by
  change RationalTerms.term (value i) 0 = residualTerms (key i)
  rw [value_eq_full, key_eq_full]
  exact BlowupF1CompleteHComponents.entries_eq (globalIndex i)

/-- The existing constructor supplies the unchanged global cache specification. -/
def indexedCache : ResidualCache X :=
  ResidualCache.ofEntries key entries keys_injective entries_eq

/-- Only this direct list is traversed by the runtime lookup. -/
def directValues : Multiset (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X)) :=
  ↑((keyList.zip valueList).map fun t ↦
    (t.1, (RationalTerms.term t.2 0 : RationalTerms (SurfaceAncestorKey X))))

theorem directList_eq_ofFn :
    (keyList.zip valueList).map (fun t ↦ (t.1, RationalTerms.term t.2 0)) =
      List.ofFn (fun i : Fin 47 ↦ (key i, entries i)) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_zip, keyList_length, valueList_length,
      Nat.min_self, List.length_ofFn]
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    rfl

theorem directValues_eq_indexed : directValues = indexedCache.values := by
  change ↑((keyList.zip valueList).map
      (fun t ↦ (t.1, (RationalTerms.term t.2 0 : RationalTerms (SurfaceAncestorKey X))))) =
    Finset.univ.val.map (fun i : Fin 47 ↦ (key i, entries i))
  rw [Fin.univ_val_map]
  exact congrArg (fun l : List (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X)) ↦
    (↑l : Multiset (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X))))
    directList_eq_ofFn

/-- Existing proof-bearing cache with a literal 47-pair runtime representation. -/
def cache : ResidualCache X where
  queries := indexedCache.queries
  values := directValues
  values_eq := directValues_eq_indexed.trans indexedCache.values_eq

theorem queries_subset_full : cache.queries ⊆ BlowupF1CompleteHComponents.cache.queries := by
  intro q hq
  change q ∈ Finset.univ.image key at hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
  change key i ∈ Finset.univ.image BlowupF1CompleteHComponents.key
  exact Finset.mem_image.mpr ⟨globalIndex i, Finset.mem_univ _, (key_eq_full i).symm⟩

/-- Every missing or selected key retains the original evaluator semantics. -/
theorem scalar_eq_original (q : SurfaceAncestorKey X) :
    cachedLowerValueLookupWithPoints X cache BlowupF1CertifiedPoints.rational
      BlowupF1CertifiedPoints.elliptic q =
      SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q :=
  cachedLowerValueLookupWithPoints_eq X cache _ _ BlowupF1CertifiedPoints.rational_eq
    BlowupF1CertifiedPoints.elliptic_eq q

end AxiomaticGW.BlowupF1Root122Components
