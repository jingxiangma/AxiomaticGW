/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.GetzlerGW
import AxiomaticGW.Surfaces.CurveClasses
import AxiomaticGWTest.Tautological.GetzlerReplay

set_option linter.privateModule false

/-!
# Getzler graph-construction and GW consumer regressions

The tests distinguish which vertex receives a self-gluing, retain the complete
exceptional curve class through nested splittings, and consume the actual
decoded Sage presentation in the final conditional GW theorem. They do not
provide a geometric surface model or compute its numerical invariants.
-/

namespace AxiomaticGWTest.Tautological.GetzlerGW

open AxiomaticGW GetzlerGraphs

private def wrongParallel : GluingExpression 1 (Fin 4) :=
  close (n := 4) (join (m := 3) (n := 3) 0 0
    (.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (.fundamental 0 (Fin 4) (by norm_num [StableArity])))

/-- Omitting the node-flag permutation makes a loop and tail. It is still a
valid genus-one graph, so stability and genus checks alone cannot detect it. -/
example : wrongParallel.stratum = columns 25 := by
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  decide

/-- The valid but different node incidence cannot fill the parallel-edge slot. -/
example : wrongParallel.graph.isomorphic? (graph 30) = false := by decide

/-- Moving a state-bearing marking to another component changes the held column. -/
example : (delta23Expression.relabel (Equiv.swap 0 3)).graph.isomorphic? (graph 3) =
    false := by decide

private def triples : Finset (SurfaceTarget.blowupTwo.Curve ×
    SurfaceTarget.blowupTwo.Curve × SurfaceTarget.blowupTwo.Curve) :=
  (SurfaceTarget.blowupTwo.splittings ![1,1,0]).biUnion fun outer ↦
    (SurfaceTarget.blowupTwo.splittings outer.1).image fun inner ↦
      (inner.1, inner.2, outer.2)

/-- Two distinct exceptional generators can each lie on any of three
components. All nine assignments, including zero factors, are retained. -/
example : triples =
    {(![1,1,0], ![0,0,0], ![0,0,0]),
     (![0,0,0], ![1,1,0], ![0,0,0]),
     (![0,0,0], ![0,0,0], ![1,1,0]),
     (![1,0,0], ![0,1,0], ![0,0,0]),
     (![1,0,0], ![0,0,0], ![0,1,0]),
     (![0,1,0], ![1,0,0], ![0,0,0]),
     (![0,0,0], ![1,0,0], ![0,1,0]),
     (![0,1,0], ![0,0,0], ![1,0,0]),
     (![0,0,0], ![0,1,0], ![1,0,0])} := by decide

/-- The executable nested enumeration equals the two effective-class sums
used by the contraction, not an enumeration of scalar energy partitions. -/
example : triples =
    (SurfaceTarget.blowupTwo.effective.splittings ![1,1,0]).biUnion fun outer ↦
      (SurfaceTarget.blowupTwo.effective.splittings outer.1).image fun inner ↦
        (inner.1, inner.2, outer.2) := by
  simp only [triples, SurfaceTarget.splittings_eq]

/-- The actual external replay reaches the full marked GW contraction
equation in E₁+E₂, under primitive geometric inputs only. -/
example {R V : Type} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {C : StableCurveCohomology R} (I : StableCurveIntegration C)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (hcompat : ∀ i, (expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (cycle x) = G.cycle x)
    (Omega : GromovWittenTheory R V SurfaceTarget.blowupTwo.Curve
      SurfaceTarget.blowupTwo.effective C) (a : Fin 4 → V) :
    (∑ i, algebraMap ℚ R (requested i) * gwChannel Omega I ![1,1,0] a i) = 0 :=
  exchange_gw_eq_zero A F N hcompat G hcycle Omega ![1,1,0] a
    GetzlerReplay.presentation GetzlerReplay.accepted

end AxiomaticGWTest.Tautological.GetzlerGW
