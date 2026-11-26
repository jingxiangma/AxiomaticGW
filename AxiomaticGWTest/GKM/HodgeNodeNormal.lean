/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeNodeNormal

/-!
# Node-normal expression convention checks

Ordered branches are retained even when quotient graph symmetry identifies
them. Node psi and external psi are distinguished; signs and both original
coefficients are tested. Empty original marking types remain permitted.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.HodgeNodeNormal

open AxiomaticGW AxiomaticGW.GKM.HodgeNodeNormal
open AxiomaticGW.AdmcyclesHodgeStrataCandidates

/-- Source decoration selects only the two ordered node labels. -/
theorem ordered_branch_powers :
    NonseparatingNode.firstPowers (S := Fin 1) none = 1 ∧
    NonseparatingNode.firstPowers (S := Fin 1) (some none) = 0 ∧
    NonseparatingNode.secondPowers (S := Fin 1) none = 0 ∧
    NonseparatingNode.secondPowers (S := Fin 1) (some none) = 1 ∧
    NonseparatingNode.firstPowers (some (some (0 : Fin 1))) = 0 ∧
    NonseparatingNode.secondPowers (some (some (0 : Fin 1))) = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Source positions are checked explicitly, rather than inferred from names. -/
theorem original_two_occurrences :
    raw11Degree2Columns 3 = rawGraph23 ∧
    raw11Degree2Columns 4 = rawGraph9 ∧
    raw11Degree2Coordinates 3 = (-1 / 288 : ℚ) ∧
    raw11Degree2Coordinates 4 = (-1 / 288 : ℚ) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Swapping the two loop branches identifies the underlying quotient classes. -/
theorem loop_branch_symmetry : rawGraph23 = rawGraph9 := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The two retained negative occurrences add; neither is silently divided out. -/
theorem packet_sign_and_multiplicity :
    packetNodePair = (-1 / 144 : ℚ) • StrataModule.basis rawGraph9 := by
  change (-1 / 288 : ℚ) • StrataModule.basis rawGraph23 +
    (-1 / 288 : ℚ) • StrataModule.basis rawGraph9 = _
  rw [loop_branch_symmetry, ← add_smul]
  norm_num

/-- Moving a node psi decoration to the old marking changes the class. -/
theorem node_psi_ne_external_psi : rawGraph9 ≠ rawGraph8 := by
  intro h
  obtain ⟨e⟩ := Quotient.exact h
  exact (by decide : (1 : ℕ) ≠ 0) (e.legPsiPower_comm 0)

/-- The same operation has codimension two with no original marked points. -/
theorem empty_original_labels :
    StrataModule.nonseparatingNodeNormal
      (StrataModule.basis (TautologicalStratum.fundamental 1
        (Option (Option (Fin 0))) (by unfold StableArity; decide))) ∈
      StrataModule.degree 2 := by
  have hd := StrataModule.basis_mem_degree
    (TautologicalStratum.fundamental 1 (Option (Option (Fin 0)))
      (by unfold StableArity; decide))
  rw [TautologicalStratum.fundamental_codimension] at hd
  exact StrataModule.nonseparatingNodeNormal_mem_degree hd

end AxiomaticGWTest.GKM.HodgeNodeNormal
