/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.KappaRealization

/-!
# Kappa generator convention regressions

Equal codimension does not identify a kappa decoration with an external psi
decoration. The new power is placed at the forgotten label, not an old label.
The stable genus-two construction also permits no original markings.
-/

@[expose] public section

namespace AxiomaticGWTest.Tautological.KappaRealization

open AxiomaticGW

/-- Fixed stable arity used by the public convention regressions. -/
theorem stable : StableArity 2 (Fin 1) := by
  unfold StableArity
  decide

/-- A vertex kappa decoration is not replaced by an equal-degree leg decoration. -/
theorem kappa_ne_external_psi :
    TautologicalStratum.kappaGenerator 2 (Fin 1) stable 1 ≠
      (TautologicalStratum.fundamental 2 (Fin 1) stable).addLegPsi (fun _ ↦ 1) := by
  intro h
  obtain ⟨e⟩ := Quotient.exact h
  exact (by decide : (1 : ℕ) ≠ 0) (e.legPsiPower_comm 0)

/-- Putting the same psi power on an old marking changes the raw stratum. -/
theorem forgotten_ne_old_marking :
    TautologicalStratum.newMarkingPsiGenerator 2 (Fin 1) stable 1 ≠
      (TautologicalStratum.fundamental 2 (Option (Fin 1)) stable.option).addLegPsi
        (fun t ↦ match t with
          | none => 0
          | some _ => 2) := by
  intro h
  obtain ⟨e⟩ := Quotient.exact h
  exact (by decide : (0 : ℕ) ≠ 2) (e.legPsiPower_comm none)

/-- Empty original marking sets are allowed when the base arity is stable. -/
theorem empty_old_markings :
    (TautologicalStratum.kappaGenerator 2 (Fin 0)
      (by unfold StableArity; decide) 2).codimension = 2 ∧
      (TautologicalStratum.newMarkingPsiGenerator 2 (Fin 0)
      (by unfold StableArity; decide) 2).codimension = 3 := by
  constructor
  · exact TautologicalStratum.kappaGenerator_codimension 2 (Fin 0)
      (by unfold StableArity; decide) 2
  · exact TautologicalStratum.newMarkingPsiGenerator_codimension 2 (Fin 0)
      (by unfold StableArity; decide) 2

end AxiomaticGWTest.Tautological.KappaRealization
