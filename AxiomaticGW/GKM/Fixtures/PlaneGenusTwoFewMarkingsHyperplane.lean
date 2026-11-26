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
# Plane few-marking arithmetic: Hyperplane

Each full query follows from separately checked ancestor equations and its
complete descendant expansion. The original canonical table is unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536
set_option cbv.maxSteps 4000000

namespace AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay.Hyperplane

open BelorousskiPandharipande

private theorem value_21 : planeQueryValueWith? canonicalValues
    (requests 21) = some (values 21) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 21) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 21

private theorem value_22 : planeQueryValueWith? canonicalValues
    (requests 22) = some (values 22) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 22) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 22

private theorem value_23 : planeQueryValueWith? canonicalValues
    (requests 23) = some (values 23) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 23) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 23

private theorem value_24 : planeQueryValueWith? canonicalValues
    (requests 24) = some (values 24) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 24) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 24

private theorem value_25 : planeQueryValueWith? canonicalValues
    (requests 25) = some (values 25) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 25) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 25

private theorem value_26 : planeQueryValueWith? canonicalValues
    (requests 26) = some (values 26) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 26) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 26

private theorem value_27 : planeQueryValueWith? canonicalValues
    (requests 27) = some (values 27) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 27) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 27

private theorem value_28 : planeQueryValueWith? canonicalValues
    (requests 28) = some (values 28) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 28) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 28

private theorem value_29 : planeQueryValueWith? canonicalValues
    (requests 29) = some (values 29) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 29) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 29

private theorem value_30 : planeQueryValueWith? canonicalValues
    (requests 30) = some (values 30) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 30) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 30

private theorem value_31 : planeQueryValueWith? canonicalValues
    (requests 31) = some (values 31) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 31) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 31

private theorem value_32 : planeQueryValueWith? canonicalValues
    (requests 32) = some (values 32) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 32) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 32

private theorem value_33 : planeQueryValueWith? canonicalValues
    (requests 33) = some (values 33) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 33) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 33

private theorem value_34 : planeQueryValueWith? canonicalValues
    (requests 34) = some (values 34) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 34) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 34

private theorem value_35 : planeQueryValueWith? canonicalValues
    (requests 35) = some (values 35) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 35) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 35

/-- Every request in this sector is checked, including its full ordered insertions. -/
theorem computed (i : Fin 15) : planeQueryValueWith? canonicalValues
    (requests ⟨21 + i.val, by omega⟩) =
      some (values ⟨21 + i.val, by omega⟩) := by
  fin_cases i
  · exact value_21
  · exact value_22
  · exact value_23
  · exact value_24
  · exact value_25
  · exact value_26
  · exact value_27
  · exact value_28
  · exact value_29
  · exact value_30
  · exact value_31
  · exact value_32
  · exact value_33
  · exact value_34
  · exact value_35

end AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay.Hyperplane
