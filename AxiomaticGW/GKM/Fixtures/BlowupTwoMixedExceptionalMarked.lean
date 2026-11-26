/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoMixedExceptional
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoMixedExceptionalOneMarking
public import AxiomaticGW.Surfaces.GenusTwoMarkedPairLookup

/-! # Mixed exceptional singletons, marked equations and exceptional point support -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoMixedExceptional
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

private theorem singleton_binding : ∀ j : Fin 5,
    (requests (Fin.castAdd 100 j), values (Fin.castAdd 100 j)) =
      (BlowupTwoMixedExceptionalOneMarking.requests j,
       BlowupTwoMixedExceptionalOneMarking.values j) := by decide +kernel

/-- The five native singletons agree with the calibrated mixed reconstruction. -/
theorem singleton_accepted (j : Fin 5) :
    queryValue? 0 (requests (Fin.castAdd 100 j)) = some (values (Fin.castAdd 100 j)) :=
  (congrArg (fun r ↦ queryValue? 0 r.1 = some r.2) (singleton_binding j)).mpr
    (BlowupTwoMixedExceptionalOneMarking.accepted j)

/-- Lookup of the original five singletons at their full class and marking. -/
def singleton? := singletonTable? BlowupTwoMixedExceptionalOneMarking.requests
  BlowupTwoMixedExceptionalOneMarking.values

/-- Pair indices covered by exceptional point support or a marked equation. -/
def reducedIndices : Finset (Fin 100) :=
  Finset.univ.filter fun i ↦ (supportedMarkedPairValueWith? singleton?
    (requests (Fin.natAdd 5 i))).isSome

/-- Point support and the marked equations resolve 68 of the 100 two-marked queries. -/
theorem card_reducedIndices : reducedIndices.card = 68 := by decide +kernel

private theorem reduced_binding : ∀ j ∈ reducedIndices, supportedMarkedPairValueWith? singleton?
    (requests (Fin.natAdd 5 j)) = some (values (Fin.natAdd 5 j)) := by decide +kernel

/-- Each reduced pair returns the native value at its exact ordered input. -/
theorem reduced_accepted {j : Fin 100} (hj : j ∈ reducedIndices) :
    CheckedDescendant 0 (requests (Fin.natAdd 5 j)) (values (Fin.natAdd 5 j)) :=
  supportedMarkedPairValueWith?_checked 0
    (singletonTable?_sound BlowupTwoMixedExceptionalOneMarking.accepted) (reduced_binding j hj)

end AxiomaticGW.GKM.BlowupTwoMixedExceptional
