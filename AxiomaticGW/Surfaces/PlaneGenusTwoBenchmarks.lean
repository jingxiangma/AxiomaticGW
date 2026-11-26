/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneTable
public import AxiomaticGW.Surfaces.PlaneGenusTwoClaim
public import AxiomaticGW.Surfaces.PlanePrimaryBenchmarks

/-!
# Certified plane genus-two canonical benchmarks

The three canonical families cover every positive plane class through
anticanonical energy twelve. Lookup checks the complete requested query and
returns no answer outside that finite suite. Its soundness theorem produces
the existing canonical claim certificate, whose geometric interpretation
retains the original class-level inputs and three finite seeds.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open BelorousskiPandharipande

/-- Lookup the held primary and first-descendant suite using the full incoming query. -/
def planeCanonicalBenchmark? (q : SurfaceQuery .plane) : Option ℚ :=
  if 0 < q.beta 0 ∧ q.beta 0 ≤ 4 then
    if q = planeCanonicalQueries (q.beta 0) 0 then
      some (PlaneGenusTwoScalarTable.values (q.beta 0) 0)
    else if q = planeCanonicalQueries (q.beta 0) 1 then
      some (PlaneGenusTwoScalarTable.values (q.beta 0) 1)
    else if q = planeCanonicalQueries (q.beta 0) 2 then
      some (PlaneGenusTwoScalarTable.values (q.beta 0) 2)
    else none
  else none

/-- A returned answer carries the existing full-query certificate, not merely a table entry. -/
theorem planeCanonicalBenchmark?_sound (q : SurfaceQuery .plane) (claimed : ℚ)
    (h : planeCanonicalBenchmark? q = some claimed) :
    planeCheckCanonicalClaim 4 PlaneGenusTwoScalarTable.values q claimed = true := by
  have bind (hb : 0 < q.beta 0 ∧ q.beta 0 ≤ 4) (j : Fin 3)
      (hq : q = planeCanonicalQueries (q.beta 0) j)
      (hv : PlaneGenusTwoScalarTable.values (q.beta 0) j = claimed) :
      planeCheckCanonicalClaim 4 PlaneGenusTwoScalarTable.values q claimed = true := by
    rw [planeCheckCanonicalClaim, PlaneGenusTwoScalarTable.accepted,
      Bool.and_true, decide_eq_true_eq]
    exact ⟨⟨q.beta 0, by omega⟩, j, hq, hv⟩
  unfold planeCanonicalBenchmark? at h
  split_ifs at h with hb h0 h1 h2
  · exact bind hb 0 h0 (Option.some.inj h)
  · exact bind hb 1 h1 (Option.some.inj h)
  · exact bind hb 2 h2 (Option.some.inj h)

/-- Every one of the twelve held queries returns its certified rational value. -/
theorem planeCanonicalBenchmark?_eq (d : ℕ) (hd : 0 < d) (hbound : d ≤ 4) (j : Fin 3) :
    planeCanonicalBenchmark? (planeCanonicalQueries d j) =
      some (PlaneGenusTwoScalarTable.values d j) := by
  interval_cases d <;> fin_cases j <;> decide +kernel

/-- The benchmark bound covers every positive effective plane class of energy at most twelve. -/
theorem planeCanonicalBenchmark_coverage (beta : SurfaceTarget.plane.Curve)
    (hbeta : beta ≠ 0) (henergy : SurfaceTarget.plane.effective.energy beta ≤ 12)
    (j : Fin 3) :
    ∃ d : Fin 4, beta = ![d.val + 1] ∧
      planeCanonicalBenchmark? (planeCanonicalQueries (d.val + 1) j) =
        some (PlaneGenusTwoScalarTable.values (d.val + 1) j) := by
  obtain ⟨d, rfl⟩ := SurfaceGenusZero.plane_primary_benchmark_coverage beta hbeta henergy
  exact ⟨d, rfl, planeCanonicalBenchmark?_eq _ (by omega) (by omega) j⟩

end AxiomaticGW.SurfaceGenusTwo
