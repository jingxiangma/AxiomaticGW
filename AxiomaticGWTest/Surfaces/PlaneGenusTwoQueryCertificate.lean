import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneFewMarkingRequests
import AxiomaticGW.Surfaces.PlaneGenusTwoQueryCertificate

open AxiomaticGW BelorousskiPandharipande

private def initialTable : ℕ → Fin 3 → ℚ := fun _ ↦ ![0, -1 / 960, 0]

set_option maxRecDepth 20000

-- Check the actual descendant, rather than accepting its ancestor terminal value.
example : planeCheckDescendantClaim 0 initialTable
    ⟨2, 0, [⟨.unit, 2⟩]⟩ (7 / 640) = true := by decide +kernel

-- A coherent exact rational encoding alone cannot certify a false numerical claim.
example : planeCheckDescendantClaim 0 initialTable
    ⟨2, 0, [⟨.unit, 2⟩]⟩ (1 / 640) = false := by decide +kernel

-- Neither another genus nor a class outside the checked table can reuse that claim.
example : planeCheckDescendantClaim 0 initialTable
    ⟨1, 0, [⟨.unit, 2⟩]⟩ (7 / 640) = false := by decide +kernel

example : planeCheckDescendantClaim 0 initialTable
    ⟨2, ![1], [⟨.unit, 2⟩]⟩ (7 / 640) = false := by decide +kernel

-- The mathematical benchmark predicate covers the independently frozen requests.
example (q : SurfaceQuery .plane) (h : PlaneFewMarkingQuery q) :
    ∃ i : Fin 48, GenusTwoPlaneFewMarkingRequests.requests i = q := by
  have hm := (mem_planeFewMarkingQueries_iff q).mpr h
  rw [← GenusTwoPlaneFewMarkingRequests.coverage] at hm
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
  exact ⟨i, hi⟩

-- There is no dimension-compatible empty request hidden by the finite enumeration.
example (q : SurfaceQuery .plane) (h : PlaneFewMarkingQuery q) :
    q.insertions ≠ [] := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin 48, GenusTwoPlaneFewMarkingRequests.requests i = q := by
    have hm := (mem_planeFewMarkingQueries_iff q).mpr h
    rw [← GenusTwoPlaneFewMarkingRequests.coverage] at hm
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    exact ⟨i, hi⟩
  clear h
  revert i
  decide +kernel
