/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.LoopSquareGluing

/-! Public consumers retain all five corolla markings and both source branch placements. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.LoopSquareGluing

open AxiomaticGW AxiomaticGW.GKM.LoopSquareGluing
open AxiomaticGW.AdmcyclesHodgeStrataCandidates

/-- The first construction starts on the stable genus-zero five-marked corolla. -/
theorem five_marked_source :
    Fintype.card (Option (Option (Option (Option (Fin 1))))) = 5 ∧
      doubleLoopSource.graph.graph.vertexCount = 1 ∧
      doubleLoopSource.graph.graph.edgeCount = 0 ∧
      doubleLoopSource.graph.graph.genus (0 : Fin 1) = 0 := by
  decide +kernel

/-- Both new edges are retained, rather than contracting one of them away. -/
theorem double_loop_has_two_edges :
    doubleLoopExpression.graph.graph.vertexCount = 1 ∧
      doubleLoopExpression.graph.graph.edgeCount = 2 ∧
      doubleLoopExpression.graph.graph.legVertex 0 = (0 : Fin 1) := by
  decide +kernel

/-- Both ordered source constructions yield the exact same actual quotient column. -/
theorem both_ordered_sources :
    parallelFirstExpression.stratum = rawGraph28 ∧
      parallelSecondExpression.stratum = rawGraph28 :=
  ⟨rawGraph28_eq_parallelFirst.symm, rawGraph28_eq_parallelSecond.symm⟩

/-- The old marking stays on the rational component after the second edge is glued. -/
theorem parallel_old_marking :
    parallelFirstExpression.graph.graph.vertexCount = 2 ∧
      parallelFirstExpression.graph.graph.edgeCount = 2 ∧
      parallelFirstExpression.graph.graph.legVertex 0 = (0 : Fin 2) ∧
      parallelFirstExpression.graph.graph.genus (0 : Fin 2) = 0 := by
  decide +kernel

end AxiomaticGWTest.GKM.LoopSquareGluing
