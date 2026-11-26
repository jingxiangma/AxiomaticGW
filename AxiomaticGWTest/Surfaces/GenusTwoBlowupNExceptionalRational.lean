/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNExceptionalRational

/-! Exact classical, generator, foreign-generator and reducible boundaries. -/

@[expose] public section

set_option linter.privateModule false

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupNExceptionalRational
open AxiomaticGW SurfaceGenusTwoBlowupNExceptionalRational

/-- The class-zero rational triple retains the negative exceptional intersection. -/
theorem classical_triple (X : SurfaceTarget) (i : Fin X.blowups) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
      0 0 ![.exceptional i, .exceptional i, .unit] = -1 := by
  rw [triple_support X i 0 (map_zero _) 0 .unit, if_pos ⟨rfl, rfl, rfl⟩]

/-- The energy-one exceptional seed and its rational quadruple contribution remain one. -/
theorem exceptional_generator_seed_preserved (X : SurfaceTarget) (i : Fin X.blowups) :
    SurfaceGenusZero.pointValue X (X.exceptionalCurve i) = 1 ∧
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
      (X.exceptionalCurve i) 0 ![.exceptional i, .exceptional i, .exceptional i,
        .exceptional i] = 1 := by
  constructor
  · exact SurfaceGenusZero.pointValue_exceptional_generator X i
  · rw [quad_support X i _ (X.planeDegree_exceptionalCurve i) 0 (.exceptional i),
      if_pos ⟨rfl, rfl, rfl⟩]

/-- A distinct exceptional generator cannot supply the selected rational node. -/
theorem foreign_generator_vanishes :
    SurfaceGenusZero.primaryScalar .blowupTwo (SurfaceGenusZero.pointValue .blowupTwo)
      (SurfaceTarget.blowupTwo.exceptionalCurve 1) 0
      ![.exceptional 0, .exceptional 0, .exceptional 0, .exceptional 0] = 0 := by
  rw [quad_support .blowupTwo 0 _
    (SurfaceTarget.blowupTwo.planeDegree_exceptionalCurve 1)]
  decide +kernel

/-- All plane-zero remainders of energy at least two vanish, including reducible classes. -/
theorem higher_energy_remainder_vanishes (X : SurfaceTarget) (i : Fin X.blowups) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (he : 2 ≤ X.effective.energy delta)
    (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) delta n
      ![.exceptional i, .exceptional i, .exceptional i, b] = 0 := by
  rw [quad_support X i delta hd n b, if_neg]
  intro h
  rw [h.1, X.energy_exceptionalCurve] at he
  omega

/-- An extra primary point is excluded even at the exceptional generator. -/
theorem added_point_excluded (X : SurfaceTarget) (i : Fin X.blowups) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
      (X.exceptionalCurve i) 1 ![.exceptional i, .exceptional i, b] = 0 := by
  rw [triple_support X i _ (X.planeDegree_exceptionalCurve i) 1 b]
  simp only [Nat.one_ne_zero, false_and, and_false, ite_false]

end AxiomaticGWTest.SurfaceGenusTwoBlowupNExceptionalRational
