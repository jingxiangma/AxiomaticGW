/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsData
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsReplay
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsDescendants

/-!
# Plane few-marking arithmetic: Unit

Each full query follows from separately checked ancestor equations and its
complete descendant expansion. The original canonical table is unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536
set_option cbv.maxSteps 4000000

namespace AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay.Unit

open BelorousskiPandharipande

private theorem value_3 : planeQueryValueWith? canonicalValues
    (requests 3) = some (values 3) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 3) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 3

private theorem value_4 : planeQueryValueWith? canonicalValues
    (requests 4) = some (values 4) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 4) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 4

private theorem value_5 : planeQueryValueWith? canonicalValues
    (requests 5) = some (values 5) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 5) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 5

private theorem value_6 : planeQueryValueWith? canonicalValues
    (requests 6) = some (values 6) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 6) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 6

private theorem value_7 : planeQueryValueWith? canonicalValues
    (requests 7) = some (values 7) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 7) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 7

private theorem value_8 : planeQueryValueWith? canonicalValues
    (requests 8) = some (values 8) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 8) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 8

private theorem value_9 : planeQueryValueWith? canonicalValues
    (requests 9) = some (values 9) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 9) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 9

private theorem value_10 : planeQueryValueWith? canonicalValues
    (requests 10) = some (values 10) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 10) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 10

private theorem value_11 : planeQueryValueWith? canonicalValues
    (requests 11) = some (values 11) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 11) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 11

private theorem value_12 : planeQueryValueWith? canonicalValues
    (requests 12) = some (values 12) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 12) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 12

private theorem value_13 : planeQueryValueWith? canonicalValues
    (requests 13) = some (values 13) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 13) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 13

private theorem value_14 : planeQueryValueWith? canonicalValues
    (requests 14) = some (values 14) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 14) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 14

private theorem value_15 : planeQueryValueWith? canonicalValues
    (requests 15) = some (values 15) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 15) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 15

private theorem value_16 : planeQueryValueWith? canonicalValues
    (requests 16) = some (values 16) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 16) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 16

private theorem value_17 : planeQueryValueWith? canonicalValues
    (requests 17) = some (values 17) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 17) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 17

private theorem value_18 : planeQueryValueWith? canonicalValues
    (requests 18) = some (values 18) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 18) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 18

private theorem value_19 : planeQueryValueWith? canonicalValues
    (requests 19) = some (values 19) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 19) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 19

private theorem value_20 : planeQueryValueWith? canonicalValues
    (requests 20) = some (values 20) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 20) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 20

/-- Every request in this sector is checked, including its full ordered insertions. -/
theorem computed (i : Fin 18) : planeQueryValueWith? canonicalValues
    (requests ⟨3 + i.val, by omega⟩) =
      some (values ⟨3 + i.val, by omega⟩) := by
  fin_cases i
  · exact value_3
  · exact value_4
  · exact value_5
  · exact value_6
  · exact value_7
  · exact value_8
  · exact value_9
  · exact value_10
  · exact value_11
  · exact value_12
  · exact value_13
  · exact value_14
  · exact value_15
  · exact value_16
  · exact value_17
  · exact value_18
  · exact value_19
  · exact value_20

end AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay.Unit
