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

Original row indices: 744,762,788.
This selection retains 63 exact full keys from the original722-entry table.
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

namespace AxiomaticGW.BlowupF1SelectedComponentsRow0744
open SurfaceGenusTwo
abbrev X := SurfaceTarget.hirzebruchOne

/-- Proof-only binding to the original accepted full-table indices. -/
def globalIndex (i : Fin 63) : Fin 722 :=
  (![
    2, 7, 12, 20, 21, 35, 39, 41, 44, 49, 65, 84, 96, 98, 110, 112, 125, 136, 138, 149, 151, 155, 163, 165, 169, 170, 176, 178, 195, 205, 207, 219, 229, 231, 241, 243, 247, 254, 256, 270, 274, 276, 279, 281, 284, 289, 310, 322, 324, 344, 357, 359, 372, 378, 387, 389, 443, 458, 473, 561, 653, 666, 668
  ] : Fin 63 → Fin 722) i

/-- Named full-key constants; no full-table array lookup is used here. -/
def keyList : List (SurfaceAncestorKey X) :=
  [
    BlowupF1CompleteHComponents.key002,
    BlowupF1CompleteHComponents.key007,
    BlowupF1CompleteHComponents.key012,
    BlowupF1CompleteHComponents.key020,
    BlowupF1CompleteHComponents.key021,
    BlowupF1CompleteHComponents.key035,
    BlowupF1CompleteHComponents.key039,
    BlowupF1CompleteHComponents.key041,
    BlowupF1CompleteHComponents.key044,
    BlowupF1CompleteHComponents.key049,
    BlowupF1CompleteHComponents.key065,
    BlowupF1CompleteHComponents.key084,
    BlowupF1CompleteHComponents.key096,
    BlowupF1CompleteHComponents.key098,
    BlowupF1CompleteHComponents.key110,
    BlowupF1CompleteHComponents.key112,
    BlowupF1CompleteHComponents.key125,
    BlowupF1CompleteHComponents.key136,
    BlowupF1CompleteHComponents.key138,
    BlowupF1CompleteHComponents.key149,
    BlowupF1CompleteHComponents.key151,
    BlowupF1CompleteHComponents.key155,
    BlowupF1CompleteHComponents.key163,
    BlowupF1CompleteHComponents.key165,
    BlowupF1CompleteHComponents.key169,
    BlowupF1CompleteHComponents.key170,
    BlowupF1CompleteHComponents.key176,
    BlowupF1CompleteHComponents.key178,
    BlowupF1CompleteHComponents.key195,
    BlowupF1CompleteHComponents.key205,
    BlowupF1CompleteHComponents.key207,
    BlowupF1CompleteHComponents.key219,
    BlowupF1CompleteHComponents.key229,
    BlowupF1CompleteHComponents.key231,
    BlowupF1CompleteHComponents.key241,
    BlowupF1CompleteHComponents.key243,
    BlowupF1CompleteHComponents.key247,
    BlowupF1CompleteHComponents.key254,
    BlowupF1CompleteHComponents.key256,
    BlowupF1CompleteHComponents.key270,
    BlowupF1CompleteHComponents.key274,
    BlowupF1CompleteHComponents.key276,
    BlowupF1CompleteHComponents.key279,
    BlowupF1CompleteHComponents.key281,
    BlowupF1CompleteHComponents.key284,
    BlowupF1CompleteHComponents.key289,
    BlowupF1CompleteHComponents.key310,
    BlowupF1CompleteHComponents.key322,
    BlowupF1CompleteHComponents.key324,
    BlowupF1CompleteHComponents.key344,
    BlowupF1CompleteHComponents.key357,
    BlowupF1CompleteHComponents.key359,
    BlowupF1CompleteHComponents.key372,
    BlowupF1CompleteHComponents.key378,
    BlowupF1CompleteHComponents.key387,
    BlowupF1CompleteHComponents.key389,
    BlowupF1CompleteHComponents.key443,
    BlowupF1CompleteHComponents.key458,
    BlowupF1CompleteHComponents.key473,
    BlowupF1CompleteHComponents.key561,
    BlowupF1CompleteHComponents.key653,
    BlowupF1CompleteHComponents.key666,
    BlowupF1CompleteHComponents.key668
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
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
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
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
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
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 8 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ)
  ]

theorem keyList_length : keyList.length = 63 := rfl
theorem valueList_length : valueList.length = 63 := rfl

def key (i : Fin 63) : SurfaceAncestorKey X :=
  keyList[i.val]'(by simpa only [keyList_length] using i.isLt)

def value (i : Fin 63) : ℚ :=
  valueList[i.val]'(by simpa only [valueList_length] using i.isLt)

def entries (i : Fin 63) : RationalTerms (SurfaceAncestorKey X) :=
  RationalTerms.term (value i) 0

theorem globalIndex_injective : Function.Injective globalIndex := by decide +kernel

set_option maxHeartbeats 0 in
theorem key_eq_full (i : Fin 63) :
    key i = BlowupF1CompleteHComponents.key (globalIndex i) := by
  fin_cases i <;> rfl

set_option maxHeartbeats 0 in
theorem value_eq_full (i : Fin 63) :
    value i = BlowupF1CompleteHComponents.value (globalIndex i) := by
  fin_cases i <;> rfl

/-- Reuse the original full-key injectivity theorem. -/
theorem keys_injective : Function.Injective key := by
  intro i j h
  apply globalIndex_injective
  apply BlowupF1CompleteHComponents.keys_injective
  exact (key_eq_full i).symm.trans (h.trans (key_eq_full j))

/-- Reuse the accepted residual equations; no ancestor algorithm is recomputed. -/
theorem entries_eq (i : Fin 63) : entries i = residualTerms (key i) := by
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
      List.ofFn (fun i : Fin 63 ↦ (key i, entries i)) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_zip, keyList_length, valueList_length,
      Nat.min_self, List.length_ofFn]
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    rfl

theorem directValues_eq_indexed : directValues = indexedCache.values := by
  change ↑((keyList.zip valueList).map
      (fun t ↦ (t.1, (RationalTerms.term t.2 0 : RationalTerms (SurfaceAncestorKey X))))) =
    Finset.univ.val.map (fun i : Fin 63 ↦ (key i, entries i))
  rw [Fin.univ_val_map]
  exact congrArg (fun l : List (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X)) ↦
    (↑l : Multiset (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X))))
    directList_eq_ofFn

/-- Existing proof-bearing cache with a literal 63-pair runtime representation. -/
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

end AxiomaticGW.BlowupF1SelectedComponentsRow0744
