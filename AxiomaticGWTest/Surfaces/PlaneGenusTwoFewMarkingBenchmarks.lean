import AxiomaticGW.Surfaces.PlaneGenusTwoFewMarkingBenchmarks

open AxiomaticGW SurfaceGenusTwo BelorousskiPandharipande

-- These two-marked requests have genuinely nonzero descendants.
example : planeFewMarkingBenchmark?
    ⟨2, ![1], [⟨.point, 1⟩, ⟨.point, 1⟩]⟩ = some (1 / 144) := by decide +kernel

example : planeFewMarkingBenchmark?
    ⟨2, ![1], [⟨.unit, 3⟩, ⟨.unit, 3⟩]⟩ = some (7 / 320) := by decide +kernel

-- The same insertions at a different full class cannot reuse a degree-one answer.
example : planeFewMarkingBenchmark?
    ⟨2, ![2], [⟨.point, 1⟩, ⟨.point, 1⟩]⟩ = none := by decide +kernel

-- A dimension-incompatible query is outside this finite lookup, not a certified zero.
example : planeFewMarkingBenchmark?
    ⟨2, ![1], [⟨.point, 0⟩, ⟨.point, 0⟩]⟩ = none := by decide +kernel

example (q : SurfaceQuery .plane) (h : PlaneFewMarkingQuery q) :
    ∃ value, planeFewMarkingBenchmark? q = some value ∧ planeQueryValue? q = some value := by
  obtain ⟨value, hv⟩ := (planeFewMarkingBenchmark?_domain q).mpr h
  exact ⟨value, hv, planeFewMarkingBenchmark?_sound q value hv⟩
