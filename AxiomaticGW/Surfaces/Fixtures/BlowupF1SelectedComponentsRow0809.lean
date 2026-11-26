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

Original row indices: 809,810,812.
This selection retains 56 exact full keys from the original722-entry table.
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

namespace AxiomaticGW.BlowupF1SelectedComponentsRow0809
open SurfaceGenusTwo
abbrev X := SurfaceTarget.hirzebruchOne

/-- Proof-only binding to the original accepted full-table indices. -/
def globalIndex (i : Fin 56) : Fin 722 :=
  (![
    2, 7, 20, 33, 40, 41, 50, 54, 63, 65, 73, 82, 84, 94, 108, 110, 120, 123, 125, 134, 147, 149, 155, 161, 169, 170, 175, 176, 186, 190, 195, 204, 205, 214, 219, 228, 229, 241, 247, 253, 254, 268, 271, 275, 276, 280, 281, 285, 290, 293, 298, 320, 332, 355, 378, 385
  ] : Fin 56 → Fin 722) i

/-- Named full-key constants; no full-table array lookup is used here. -/
def keyList : List (SurfaceAncestorKey X) :=
  [
    BlowupF1CompleteHComponents.key002,
    BlowupF1CompleteHComponents.key007,
    BlowupF1CompleteHComponents.key020,
    BlowupF1CompleteHComponents.key033,
    BlowupF1CompleteHComponents.key040,
    BlowupF1CompleteHComponents.key041,
    BlowupF1CompleteHComponents.key050,
    BlowupF1CompleteHComponents.key054,
    BlowupF1CompleteHComponents.key063,
    BlowupF1CompleteHComponents.key065,
    BlowupF1CompleteHComponents.key073,
    BlowupF1CompleteHComponents.key082,
    BlowupF1CompleteHComponents.key084,
    BlowupF1CompleteHComponents.key094,
    BlowupF1CompleteHComponents.key108,
    BlowupF1CompleteHComponents.key110,
    BlowupF1CompleteHComponents.key120,
    BlowupF1CompleteHComponents.key123,
    BlowupF1CompleteHComponents.key125,
    BlowupF1CompleteHComponents.key134,
    BlowupF1CompleteHComponents.key147,
    BlowupF1CompleteHComponents.key149,
    BlowupF1CompleteHComponents.key155,
    BlowupF1CompleteHComponents.key161,
    BlowupF1CompleteHComponents.key169,
    BlowupF1CompleteHComponents.key170,
    BlowupF1CompleteHComponents.key175,
    BlowupF1CompleteHComponents.key176,
    BlowupF1CompleteHComponents.key186,
    BlowupF1CompleteHComponents.key190,
    BlowupF1CompleteHComponents.key195,
    BlowupF1CompleteHComponents.key204,
    BlowupF1CompleteHComponents.key205,
    BlowupF1CompleteHComponents.key214,
    BlowupF1CompleteHComponents.key219,
    BlowupF1CompleteHComponents.key228,
    BlowupF1CompleteHComponents.key229,
    BlowupF1CompleteHComponents.key241,
    BlowupF1CompleteHComponents.key247,
    BlowupF1CompleteHComponents.key253,
    BlowupF1CompleteHComponents.key254,
    BlowupF1CompleteHComponents.key268,
    BlowupF1CompleteHComponents.key271,
    BlowupF1CompleteHComponents.key275,
    BlowupF1CompleteHComponents.key276,
    BlowupF1CompleteHComponents.key280,
    BlowupF1CompleteHComponents.key281,
    BlowupF1CompleteHComponents.key285,
    BlowupF1CompleteHComponents.key290,
    BlowupF1CompleteHComponents.key293,
    BlowupF1CompleteHComponents.key298,
    BlowupF1CompleteHComponents.key320,
    BlowupF1CompleteHComponents.key332,
    BlowupF1CompleteHComponents.key355,
    BlowupF1CompleteHComponents.key378,
    BlowupF1CompleteHComponents.key385
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
    (0 / 1 : ℚ)
  ]

theorem keyList_length : keyList.length = 56 := rfl
theorem valueList_length : valueList.length = 56 := rfl

def key (i : Fin 56) : SurfaceAncestorKey X :=
  keyList[i.val]'(by simpa only [keyList_length] using i.isLt)

def value (i : Fin 56) : ℚ :=
  valueList[i.val]'(by simpa only [valueList_length] using i.isLt)

def entries (i : Fin 56) : RationalTerms (SurfaceAncestorKey X) :=
  RationalTerms.term (value i) 0

theorem globalIndex_injective : Function.Injective globalIndex := by decide +kernel

set_option maxHeartbeats 0 in
theorem key_eq_full (i : Fin 56) :
    key i = BlowupF1CompleteHComponents.key (globalIndex i) := by
  fin_cases i <;> rfl

set_option maxHeartbeats 0 in
theorem value_eq_full (i : Fin 56) :
    value i = BlowupF1CompleteHComponents.value (globalIndex i) := by
  fin_cases i <;> rfl

/-- Reuse the original full-key injectivity theorem. -/
theorem keys_injective : Function.Injective key := by
  intro i j h
  apply globalIndex_injective
  apply BlowupF1CompleteHComponents.keys_injective
  exact (key_eq_full i).symm.trans (h.trans (key_eq_full j))

/-- Reuse the accepted residual equations; no ancestor algorithm is recomputed. -/
theorem entries_eq (i : Fin 56) : entries i = residualTerms (key i) := by
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
      List.ofFn (fun i : Fin 56 ↦ (key i, entries i)) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_zip, keyList_length, valueList_length,
      Nat.min_self, List.length_ofFn]
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    rfl

theorem directValues_eq_indexed : directValues = indexedCache.values := by
  change ↑((keyList.zip valueList).map
      (fun t ↦ (t.1, (RationalTerms.term t.2 0 : RationalTerms (SurfaceAncestorKey X))))) =
    Finset.univ.val.map (fun i : Fin 56 ↦ (key i, entries i))
  rw [Fin.univ_val_map]
  exact congrArg (fun l : List (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X)) ↦
    (↑l : Multiset (SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X))))
    directList_eq_ofFn

/-- Existing proof-bearing cache with a literal 56-pair runtime representation. -/
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

end AxiomaticGW.BlowupF1SelectedComponentsRow0809
