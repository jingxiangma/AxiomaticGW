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

Original row indices: 124,142,157.
This selection retains 55 exact full keys from the original722-entry table.
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

namespace AxiomaticGW.BlowupF1SelectedComponentsRow0124
open SurfaceGenusTwo
abbrev X := SurfaceTarget.hirzebruchOne

/-- Proof-only binding to the original accepted full-table indices. -/
def globalIndex (i : Fin 55) : Fin 722 :=
  (![
    26, 46, 117, 156, 169, 170, 182, 183, 248, 260, 261, 281, 286, 379, 393, 394, 410, 424, 428, 429, 443, 449, 452, 458, 464, 467, 471, 473, 504, 519, 523, 525, 530, 531, 535, 537, 538, 539, 561, 586, 590, 592, 618, 634, 638, 639, 644, 648, 649, 653, 666, 668, 695, 700, 702
  ] : Fin 55 → Fin 722) i

/-- Named full-key constants; no full-table array lookup is used here. -/
def keyList : List (SurfaceAncestorKey X) :=
  [
    BlowupF1CompleteHComponents.key026,
    BlowupF1CompleteHComponents.key046,
    BlowupF1CompleteHComponents.key117,
    BlowupF1CompleteHComponents.key156,
    BlowupF1CompleteHComponents.key169,
    BlowupF1CompleteHComponents.key170,
    BlowupF1CompleteHComponents.key182,
    BlowupF1CompleteHComponents.key183,
    BlowupF1CompleteHComponents.key248,
    BlowupF1CompleteHComponents.key260,
    BlowupF1CompleteHComponents.key261,
    BlowupF1CompleteHComponents.key281,
    BlowupF1CompleteHComponents.key286,
    BlowupF1CompleteHComponents.key379,
    BlowupF1CompleteHComponents.key393,
    BlowupF1CompleteHComponents.key394,
    BlowupF1CompleteHComponents.key410,
    BlowupF1CompleteHComponents.key424,
    BlowupF1CompleteHComponents.key428,
    BlowupF1CompleteHComponents.key429,
    BlowupF1CompleteHComponents.key443,
    BlowupF1CompleteHComponents.key449,
    BlowupF1CompleteHComponents.key452,
    BlowupF1CompleteHComponents.key458,
    BlowupF1CompleteHComponents.key464,
    BlowupF1CompleteHComponents.key467,
    BlowupF1CompleteHComponents.key471,
    BlowupF1CompleteHComponents.key473,
    BlowupF1CompleteHComponents.key504,
    BlowupF1CompleteHComponents.key519,
    BlowupF1CompleteHComponents.key523,
    BlowupF1CompleteHComponents.key525,
    BlowupF1CompleteHComponents.key530,
    BlowupF1CompleteHComponents.key531,
    BlowupF1CompleteHComponents.key535,
    BlowupF1CompleteHComponents.key537,
    BlowupF1CompleteHComponents.key538,
    BlowupF1CompleteHComponents.key539,
    BlowupF1CompleteHComponents.key561,
    BlowupF1CompleteHComponents.key586,
    BlowupF1CompleteHComponents.key590,
    BlowupF1CompleteHComponents.key592,
    BlowupF1CompleteHComponents.key618,
    BlowupF1CompleteHComponents.key634,
    BlowupF1CompleteHComponents.key638,
    BlowupF1CompleteHComponents.key639,
    BlowupF1CompleteHComponents.key644,
    BlowupF1CompleteHComponents.key648,
    BlowupF1CompleteHComponents.key649,
    BlowupF1CompleteHComponents.key653,
    BlowupF1CompleteHComponents.key666,
    BlowupF1CompleteHComponents.key668,
    BlowupF1CompleteHComponents.key695,
    BlowupF1CompleteHComponents.key700,
    BlowupF1CompleteHComponents.key702
  ]

/-- Original exact signed values in the same selected order. -/
def valueList : List ℚ :=
  [
    (1 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 1 : ℚ),
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
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
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
    (0 / 1 : ℚ),
    (0 / 1 : ℚ)
  ]

theorem keyList_length : keyList.length = 55 := rfl
theorem valueList_length : valueList.length = 55 := rfl

def key (i : Fin 55) : SurfaceAncestorKey X :=
  keyList[i.val]'(by simpa only [keyList_length] using i.isLt)

def value (i : Fin 55) : ℚ :=
  valueList[i.val]'(by simpa only [valueList_length] using i.isLt)

def entries (i : Fin 55) : RationalTerms (SurfaceAncestorKey X) :=
  RationalTerms.term (value i) 0

theorem globalIndex_injective : Function.Injective globalIndex := by decide +kernel

set_option maxHeartbeats 0 in
theorem key_eq_full (i : Fin 55) :
    key i = BlowupF1CompleteHComponents.key (globalIndex i) := by
  fin_cases i <;> rfl

set_option maxHeartbeats 0 in
theorem value_eq_full (i : Fin 55) :
    value i = BlowupF1CompleteHComponents.value (globalIndex i) := by
  fin_cases i <;> rfl

/-- Reuse the original full-key injectivity theorem. -/
theorem keys_injective : Function.Injective key := by
  intro i j h
  apply globalIndex_injective
  apply BlowupF1CompleteHComponents.keys_injective
  exact (key_eq_full i).symm.trans (h.trans (key_eq_full j))

/-- Reuse the accepted residual equations; no ancestor algorithm is recomputed. -/
theorem entries_eq (i : Fin 55) : entries i = residualTerms (key i) := by
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
      List.ofFn (fun i : Fin 55 ↦ (key i, entries i)) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_zip, keyList_length, valueList_length,
      Nat.min_self, List.length_ofFn]
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    rfl

theorem directValues_eq_indexed : directValues = indexedCache.values := by
  change ↑((keyList.zip valueList).map
      (fun t ↦ (t.1, (RationalTerms.term t.2 0 : RationalTerms (SurfaceAncestorKey X))))) =
    Finset.univ.val.map (fun i : Fin 55 ↦ (key i, entries i))
  rw [Fin.univ_val_map]
  exact congrArg (fun l : List (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X)) ↦
    (↑l : Multiset (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X))))
    directList_eq_ofFn

/-- Existing proof-bearing cache with a literal 55-pair runtime representation. -/
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

end AxiomaticGW.BlowupF1SelectedComponentsRow0124
