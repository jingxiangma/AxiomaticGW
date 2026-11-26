module

public import AxiomaticGW.Surfaces.GenusTwoBlowupBoundaryBenchmarks

@[expose] public section

namespace AxiomaticGWTest.GenusTwoBlowupBoundaryBenchmarks
open AxiomaticGW SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupBoundaryBenchmarks

attribute [local irreducible] requests classes

/-- A mixed exceptional class is included at the upper energy bound, with either
exceptional sector and either choice of the pivot in the original recursion. -/
theorem mixed_top (i j : Fin 2) :
    (state? ((Family.exceptional j : Family .blowupTwo).query ![6, 6, 0])).map
      (SurfaceGenusTwoBlowupRecursion.values (X := .blowupTwo) i) = some 0 := by
  apply reconstructed (X := .blowupTwo) i
  apply query_mem (X := .blowupTwo) ![6, 6, 0] (.exceptional j)
  rw [mem_classes]
  decide +kernel

/-- The strict line shares the exceptional generators' energy and has positive plane degree. -/
theorem strict_line_excluded :
    (Family.primary (X := .blowupTwo)).query ![0, 0, 1] ∉ requests .blowupTwo := by
  intro h
  have hd := ((mem_requests (X := .blowupTwo)
    ((Family.primary (X := .blowupTwo)).query ![0, 0, 1])).mp h).2.1
  exact (by decide +kernel : ¬SurfaceTarget.blowupTwo.planeDegree ![0, 0, 1] = 0) hd

/-- The energy cut also excludes genuine positive exceptional classes above twelve. -/
theorem first_blowup_above_bound :
    (Family.hyperplane (X := .hirzebruchOne)).query ![13, 0] ∉ requests .hirzebruchOne := by
  intro h
  have he := ((mem_requests (X := .hirzebruchOne)
    ((Family.hyperplane (X := .hirzebruchOne)).query ![13, 0])).mp h).2.2.1
  exact (by decide +kernel : ¬SurfaceTarget.hirzebruchOne.effective.energy ![13, 0] ≤ 12) he

/-- The canonical exceptional-divisor seed at class zero lies outside the positive boundary. -/
theorem zero_class_excluded :
    (Family.exceptional 0 : Family .hirzebruchOne).query 0 ∉ requests .hirzebruchOne := by
  intro h
  exact ((mem_requests _).mp h).1 rfl

/-- A dimension-compatible unit descendant at the same curve has a different full shape. -/
theorem unit_cube_excluded :
    (⟨2, ![1, 0], [⟨.unit, 3⟩]⟩ : SurfaceQuery .hirzebruchOne) ∉ requests .hirzebruchOne := by
  intro h
  have hm := ((mem_requests _).mp h).2.2.2
  exact (by decide +kernel : (⟨2, ![1, 0], [⟨.unit, 3⟩]⟩ : SurfaceQuery .hirzebruchOne) ∉
    SurfaceGenusTwo.canonicalQueries .hirzebruchOne ![1, 0]) hm

end AxiomaticGWTest.GenusTwoBlowupBoundaryBenchmarks
