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
# Plane few-marking arithmetic: Point

Each full query follows from separately checked ancestor equations and its
complete descendant expansion. The original canonical table is unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536
set_option cbv.maxSteps 4000000

namespace AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay.Point

open BelorousskiPandharipande

private theorem value_36 : planeQueryValueWith? canonicalValues
    (requests 36) = some (values 36) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 36) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 36

private theorem value_37 : planeQueryValueWith? canonicalValues
    (requests 37) = some (values 37) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 37) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 37

private theorem value_38 : planeQueryValueWith? canonicalValues
    (requests 38) = some (values 38) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 38) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 38

private theorem value_39 : planeQueryValueWith? canonicalValues
    (requests 39) = some (values 39) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 39) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 39

private theorem value_40 : planeQueryValueWith? canonicalValues
    (requests 40) = some (values 40) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 40) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 40

private theorem value_41 : planeQueryValueWith? canonicalValues
    (requests 41) = some (values 41) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 41) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 41

private theorem value_42 : planeQueryValueWith? canonicalValues
    (requests 42) = some (values 42) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 42) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 42

private theorem value_43 : planeQueryValueWith? canonicalValues
    (requests 43) = some (values 43) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 43) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 43

private theorem value_44 : planeQueryValueWith? canonicalValues
    (requests 44) = some (values 44) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 44) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 44

private theorem value_45 : planeQueryValueWith? canonicalValues
    (requests 45) = some (values 45) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 45) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 45

private theorem value_46 : planeQueryValueWith? canonicalValues
    (requests 46) = some (values 46) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 46) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 46

private theorem value_47 : planeQueryValueWith? canonicalValues
    (requests 47) = some (values 47) := by
  change planeQueryValueWith? GenusTwoPlaneLine.values (requests 47) = _
  rw [← PlaneGenusTwoAncestors.query_eq]
  exact PlaneGenusTwoAncestors.cached_computation 47

/-- Every request in this sector is checked, including its full ordered insertions. -/
theorem computed (i : Fin 12) : planeQueryValueWith? canonicalValues
    (requests ⟨36 + i.val, by omega⟩) =
      some (values ⟨36 + i.val, by omega⟩) := by
  fin_cases i
  · exact value_36
  · exact value_37
  · exact value_38
  · exact value_39
  · exact value_40
  · exact value_41
  · exact value_42
  · exact value_43
  · exact value_44
  · exact value_45
  · exact value_46
  · exact value_47

end AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay.Point
