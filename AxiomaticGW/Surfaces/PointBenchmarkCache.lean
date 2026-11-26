/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneBenchmarks

/-!
# Total primary point backends from the certified energy-twelve benchmarks

The existing benchmark theorems identify each table entry with the original
well-founded evaluator throughout its proved bound, including the auxiliary
zero-class convention. Outside the bound the original evaluator is used.
Thus no missing table entry becomes a zero answer, and classes of energy
thirteen arising from shifted reconstruction sources remain supported.
This module sits above the benchmark fixtures; generic recursions do not
depend on this numerical specialization.
-/

@[expose] public section

namespace AxiomaticGW.SurfacePointBenchmarkCache

/-- Reuse a certified rational point entry, with the original evaluator outside its bound. -/
def genusZero (X : SurfaceTarget) (beta : X.Curve) : ℚ :=
  if X.effective.energy beta ≤ 12 then SurfaceGenusZero.pointBenchmarkValues X beta
  else SurfaceGenusZero.pointValue X beta

/-- Reuse a certified elliptic point entry, with the original evaluator outside its bound. -/
def genusOne (X : SurfaceTarget) (beta : X.Curve) : ℚ :=
  if X.effective.energy beta ≤ 12 then SurfaceGenusOne.pointBenchmarkValues X beta
  else SurfaceGenusOne.pointValue X beta

/-- The rational backend agrees as a function on all full curve classes. -/
theorem genusZero_eq (X : SurfaceTarget) : genusZero X = SurfaceGenusZero.pointValue X := by
  funext beta
  unfold genusZero
  split_ifs with hb
  · exact SurfaceGenusZero.pointBenchmarkValues_eq X beta hb
  · rfl

/-- The elliptic backend agrees as a function on all full curve classes. -/
theorem genusOne_eq (X : SurfaceTarget) : genusOne X = SurfaceGenusOne.pointValue X := by
  funext beta
  unfold genusOne
  split_ifs with hb
  · exact SurfaceGenusOne.pointBenchmarkValues_eq X beta hb
  · rfl

end AxiomaticGW.SurfacePointBenchmarkCache
