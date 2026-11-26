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

Original row indices: 179.
This selection retains 53 exact full keys from the original722-entry table.
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

namespace AxiomaticGW.BlowupF1SelectedComponentsRow0179
open SurfaceGenusTwo
abbrev X := SurfaceTarget.hirzebruchOne

/-- Proof-only binding to the original accepted full-table indices. -/
def globalIndex (i : Fin 53) : Fin 722 :=
  (![
    26, 47, 117, 156, 167, 170, 180, 182, 183, 248, 258, 261, 282, 287, 379, 391, 394, 414, 431, 432, 442, 443, 445, 454, 459, 469, 474, 509, 532, 541, 542, 543, 547, 548, 557, 559, 560, 561, 599, 608, 610, 624, 641, 642, 651, 652, 653, 655, 665, 666, 709, 719, 721
  ] : Fin 53 → Fin 722) i

/-- Named full-key constants; no full-table array lookup is used here. -/
def keyList : List (SurfaceAncestorKey X) :=
  [
    BlowupF1CompleteHComponents.key026,
    BlowupF1CompleteHComponents.key047,
    BlowupF1CompleteHComponents.key117,
    BlowupF1CompleteHComponents.key156,
    BlowupF1CompleteHComponents.key167,
    BlowupF1CompleteHComponents.key170,
    BlowupF1CompleteHComponents.key180,
    BlowupF1CompleteHComponents.key182,
    BlowupF1CompleteHComponents.key183,
    BlowupF1CompleteHComponents.key248,
    BlowupF1CompleteHComponents.key258,
    BlowupF1CompleteHComponents.key261,
    BlowupF1CompleteHComponents.key282,
    BlowupF1CompleteHComponents.key287,
    BlowupF1CompleteHComponents.key379,
    BlowupF1CompleteHComponents.key391,
    BlowupF1CompleteHComponents.key394,
    BlowupF1CompleteHComponents.key414,
    BlowupF1CompleteHComponents.key431,
    BlowupF1CompleteHComponents.key432,
    BlowupF1CompleteHComponents.key442,
    BlowupF1CompleteHComponents.key443,
    BlowupF1CompleteHComponents.key445,
    BlowupF1CompleteHComponents.key454,
    BlowupF1CompleteHComponents.key459,
    BlowupF1CompleteHComponents.key469,
    BlowupF1CompleteHComponents.key474,
    BlowupF1CompleteHComponents.key509,
    BlowupF1CompleteHComponents.key532,
    BlowupF1CompleteHComponents.key541,
    BlowupF1CompleteHComponents.key542,
    BlowupF1CompleteHComponents.key543,
    BlowupF1CompleteHComponents.key547,
    BlowupF1CompleteHComponents.key548,
    BlowupF1CompleteHComponents.key557,
    BlowupF1CompleteHComponents.key559,
    BlowupF1CompleteHComponents.key560,
    BlowupF1CompleteHComponents.key561,
    BlowupF1CompleteHComponents.key599,
    BlowupF1CompleteHComponents.key608,
    BlowupF1CompleteHComponents.key610,
    BlowupF1CompleteHComponents.key624,
    BlowupF1CompleteHComponents.key641,
    BlowupF1CompleteHComponents.key642,
    BlowupF1CompleteHComponents.key651,
    BlowupF1CompleteHComponents.key652,
    BlowupF1CompleteHComponents.key653,
    BlowupF1CompleteHComponents.key655,
    BlowupF1CompleteHComponents.key665,
    BlowupF1CompleteHComponents.key666,
    BlowupF1CompleteHComponents.key709,
    BlowupF1CompleteHComponents.key719,
    BlowupF1CompleteHComponents.key721
  ]

/-- Original exact signed values in the same selected order. -/
def valueList : List ℚ :=
  [
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
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
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 8 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 8 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
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
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ)
  ]

theorem keyList_length : keyList.length = 53 := rfl
theorem valueList_length : valueList.length = 53 := rfl

def key (i : Fin 53) : SurfaceAncestorKey X :=
  keyList[i.val]'(by simpa only [keyList_length] using i.isLt)

def value (i : Fin 53) : ℚ :=
  valueList[i.val]'(by simpa only [valueList_length] using i.isLt)

def entries (i : Fin 53) : RationalTerms (SurfaceAncestorKey X) :=
  RationalTerms.term (value i) 0

theorem globalIndex_injective : Function.Injective globalIndex := by decide +kernel

set_option maxHeartbeats 0 in
theorem key_eq_full (i : Fin 53) :
    key i = BlowupF1CompleteHComponents.key (globalIndex i) := by
  fin_cases i <;> rfl

set_option maxHeartbeats 0 in
theorem value_eq_full (i : Fin 53) :
    value i = BlowupF1CompleteHComponents.value (globalIndex i) := by
  fin_cases i <;> rfl

/-- Reuse the original full-key injectivity theorem. -/
theorem keys_injective : Function.Injective key := by
  intro i j h
  apply globalIndex_injective
  apply BlowupF1CompleteHComponents.keys_injective
  exact (key_eq_full i).symm.trans (h.trans (key_eq_full j))

/-- Reuse the accepted residual equations; no ancestor algorithm is recomputed. -/
theorem entries_eq (i : Fin 53) : entries i = residualTerms (key i) := by
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
      List.ofFn (fun i : Fin 53 ↦ (key i, entries i)) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_zip, keyList_length, valueList_length,
      Nat.min_self, List.length_ofFn]
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    rfl

theorem directValues_eq_indexed : directValues = indexedCache.values := by
  change ↑((keyList.zip valueList).map
      (fun t ↦ (t.1, (RationalTerms.term t.2 0 : RationalTerms (SurfaceAncestorKey X))))) =
    Finset.univ.val.map (fun i : Fin 53 ↦ (key i, entries i))
  rw [Fin.univ_val_map]
  exact congrArg (fun l : List (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X)) ↦
    (↑l : Multiset (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X))))
    directList_eq_ofFn

/-- Existing proof-bearing cache with a literal 53-pair runtime representation. -/
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

end AxiomaticGW.BlowupF1SelectedComponentsRow0179
