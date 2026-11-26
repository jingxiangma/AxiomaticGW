/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsReplay

/-!
# Certified lookup for every plane genus-two few-marking benchmark

The full incoming ordered query selects a checked value. The lookup covers
exactly the fixed positive-energy, at-most-two-marking domain, including its
higher cotangent powers. Soundness identifies each returned value with the
original descendant algorithm. Its geometric interpretation therefore uses
the existing plane theorem and its unchanged geometric inputs and seeds.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open BelorousskiPandharipande GKM.PlaneGenusTwoFewMarkingsReplay

/-- Exact finite lookup; an unsupported full query returns no answer. -/
def planeFewMarkingBenchmark? (q : SurfaceQuery .plane) : Option ℚ :=
  ((List.finRange 48).find? (fun i ↦ decide (requests i = q))).map values

/-- The certificate belongs to the returned query and value, including insertion order. -/
theorem planeFewMarkingBenchmark?_sound (q : SurfaceQuery .plane) (claimed : ℚ)
    (h : planeFewMarkingBenchmark? q = some claimed) :
    planeQueryValue? q = some claimed := by
  obtain ⟨i, hi, hv⟩ := Option.map_eq_some_iff.mp h
  have hq : requests i = q :=
    of_decide_eq_true (List.find?_some (p := fun j ↦ decide (requests j = q)) hi)
  rw [← hq, ← hv]
  exact accepted i

/-- Every held request returns its separately certified value. -/
theorem planeFewMarkingBenchmark?_request (i : Fin 48) :
    planeFewMarkingBenchmark? (requests i) = some (values i) := by
  revert i
  decide +kernel

/-- No benchmark query is omitted and no outside request is reported as a value. -/
theorem planeFewMarkingBenchmark?_domain (q : SurfaceQuery .plane) :
    (∃ value, planeFewMarkingBenchmark? q = some value) ↔ PlaneFewMarkingQuery q := by
  constructor
  · rintro ⟨value, h⟩
    obtain ⟨i, hi, _⟩ := Option.map_eq_some_iff.mp h
    have hq : requests i = q :=
      of_decide_eq_true (List.find?_some (p := fun j ↦ decide (requests j = q)) hi)
    apply (mem_planeFewMarkingQueries_iff q).mp
    rw [← GenusTwoPlaneFewMarkingRequests.coverage]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (coverage i).symm.trans hq⟩
  · intro hq
    have hmem := (mem_planeFewMarkingQueries_iff q).mpr hq
    rw [← GenusTwoPlaneFewMarkingRequests.coverage] at hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    have hreq : requests i = q := (coverage i).trans hi
    exact ⟨values i, hreq ▸ planeFewMarkingBenchmark?_request i⟩

end AxiomaticGW.SurfaceGenusTwo
