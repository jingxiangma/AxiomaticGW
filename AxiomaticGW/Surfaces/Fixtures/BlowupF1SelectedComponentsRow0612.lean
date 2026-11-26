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
# A direct-list certified cache shared by fixed F1 root rows

Original row indices: 612,620,624.
This selection retains 43 exact full keys from the original722-entry table.
Every stored equation reuses the accepted global proof; direct list lookup avoids
full-table indexing. Coverage is a performance hint, never a proof assumption.
The existing fallback handles every unlisted key. No root-slot value is claimed.

The original frame has815 terms (721 with nonzero coefficients); source curve
(E,F)=(1,1), one added point and labels H,E0,E0,E0 remain unchanged.
Selector-log SHA256: a5c4c41abad31443bffce2ffd25e3033c4746a82c1ef4ba144644d1e583a82f1
-/

@[expose] public section
set_option maxRecDepth 65536
set_option Elab.async false
set_option autoImplicit false

namespace AxiomaticGW.BlowupF1SelectedComponentsRow0612
open SurfaceGenusTwo
abbrev X := SurfaceTarget.hirzebruchOne

/-- Proof-only binding to the original accepted full-table indices. -/
def globalIndex (i : Fin 43) : Fin 722 :=
  (![
    23, 38, 48, 98, 112, 114, 138, 151, 153, 156, 165, 170, 178, 180, 207, 231, 245, 248, 256, 258, 273, 278, 283, 288, 324, 359, 379, 389, 433, 441, 466, 470, 475, 531, 546, 547, 558, 598, 643, 651, 656, 664, 708
  ] : Fin 43 → Fin 722) i

/-- Named full-key constants; no full-table array lookup is used here. -/
def keyList : List (SurfaceAncestorKey X) :=
  [
    BlowupF1CompleteHComponents.key023,
    BlowupF1CompleteHComponents.key038,
    BlowupF1CompleteHComponents.key048,
    BlowupF1CompleteHComponents.key098,
    BlowupF1CompleteHComponents.key112,
    BlowupF1CompleteHComponents.key114,
    BlowupF1CompleteHComponents.key138,
    BlowupF1CompleteHComponents.key151,
    BlowupF1CompleteHComponents.key153,
    BlowupF1CompleteHComponents.key156,
    BlowupF1CompleteHComponents.key165,
    BlowupF1CompleteHComponents.key170,
    BlowupF1CompleteHComponents.key178,
    BlowupF1CompleteHComponents.key180,
    BlowupF1CompleteHComponents.key207,
    BlowupF1CompleteHComponents.key231,
    BlowupF1CompleteHComponents.key245,
    BlowupF1CompleteHComponents.key248,
    BlowupF1CompleteHComponents.key256,
    BlowupF1CompleteHComponents.key258,
    BlowupF1CompleteHComponents.key273,
    BlowupF1CompleteHComponents.key278,
    BlowupF1CompleteHComponents.key283,
    BlowupF1CompleteHComponents.key288,
    BlowupF1CompleteHComponents.key324,
    BlowupF1CompleteHComponents.key359,
    BlowupF1CompleteHComponents.key379,
    BlowupF1CompleteHComponents.key389,
    BlowupF1CompleteHComponents.key433,
    BlowupF1CompleteHComponents.key441,
    BlowupF1CompleteHComponents.key466,
    BlowupF1CompleteHComponents.key470,
    BlowupF1CompleteHComponents.key475,
    BlowupF1CompleteHComponents.key531,
    BlowupF1CompleteHComponents.key546,
    BlowupF1CompleteHComponents.key547,
    BlowupF1CompleteHComponents.key558,
    BlowupF1CompleteHComponents.key598,
    BlowupF1CompleteHComponents.key643,
    BlowupF1CompleteHComponents.key651,
    BlowupF1CompleteHComponents.key656,
    BlowupF1CompleteHComponents.key664,
    BlowupF1CompleteHComponents.key708
  ]

/-- Original exact signed values in the same selected order. -/
def valueList : List ℚ :=
  [
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ)
  ]

theorem keyList_length : keyList.length = 43 := rfl
theorem valueList_length : valueList.length = 43 := rfl

def key (i : Fin 43) : SurfaceAncestorKey X :=
  keyList[i.val]'(by simpa only [keyList_length] using i.isLt)

def value (i : Fin 43) : ℚ :=
  valueList[i.val]'(by simpa only [valueList_length] using i.isLt)

def entries (i : Fin 43) : RationalTerms (SurfaceAncestorKey X) :=
  RationalTerms.term (value i) 0

theorem globalIndex_injective : Function.Injective globalIndex := by decide +kernel

set_option maxHeartbeats 0 in
theorem key_eq_full (i : Fin 43) :
    key i = BlowupF1CompleteHComponents.key (globalIndex i) := by
  fin_cases i <;> rfl

set_option maxHeartbeats 0 in
theorem value_eq_full (i : Fin 43) :
    value i = BlowupF1CompleteHComponents.value (globalIndex i) := by
  fin_cases i <;> rfl

/-- Reuse the original full-key injectivity theorem. -/
theorem keys_injective : Function.Injective key := by
  intro i j h
  apply globalIndex_injective
  apply BlowupF1CompleteHComponents.keys_injective
  exact (key_eq_full i).symm.trans (h.trans (key_eq_full j))

/-- Reuse the accepted residual equations; no ancestor algorithm is recomputed. -/
theorem entries_eq (i : Fin 43) : entries i = residualTerms (key i) := by
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
      List.ofFn (fun i : Fin 43 ↦ (key i, entries i)) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_zip, keyList_length, valueList_length,
      Nat.min_self, List.length_ofFn]
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    rfl

theorem directValues_eq_indexed : directValues = indexedCache.values := by
  change ↑((keyList.zip valueList).map
      (fun t ↦ (t.1, (RationalTerms.term t.2 0 : RationalTerms (SurfaceAncestorKey X))))) =
    Finset.univ.val.map (fun i : Fin 43 ↦ (key i, entries i))
  rw [Fin.univ_val_map]
  exact congrArg (fun l : List (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X)) ↦
    (↑l : Multiset (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X))))
    directList_eq_ofFn

/-- Existing proof-bearing cache with a literal 43-pair runtime representation. -/
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

end AxiomaticGW.BlowupF1SelectedComponentsRow0612
