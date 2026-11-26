/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.FixedGraphSupport

/-! # Shape of a connected support with one sheet in total -/

public section
namespace AxiomaticGW.GKM.FixedGraphSupport
open CurveConventionCertificate (Tables)
variable {X : SurfaceTarget} {n r v e : ℕ} {T : Tables X n r}

/-- Positivity of covering multiplicities forces a single edge if their sum is one. -/
theorem edgeCount_of_cover_sum_one (G : FixedGraphSupport T v e)
    (hs : ∑ j, (G.cover j : ℕ) = 1) : e = 1 := by
  have he : e ≤ 1 := by
    calc
      e = ∑ _ : Fin e, 1 := by simp
      _ ≤ ∑ j, (G.cover j : ℕ) := Finset.sum_le_sum fun j _ ↦ (G.cover j).pos
      _ = 1 := hs
  cases e with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.zero_ne_one] at hs
  | succ e => omega

/-- With a single edge, connectivity places every vertex at one of its ends. -/
theorem vertex_end_of_single (G : FixedGraphSupport T v 1) (m : Fin v) :
    m = G.endpoint 0 0 ∨ m = G.endpoint 0 1 := by
  have path := (StableGraphCode.reachable_iff G.endpoint _ _).mp
    (G.connected.preconnected (G.endpoint 0 0) m)
  induction path with
  | refl => exact Or.inl rfl
  | tail _ step _ =>
    obtain ⟨j, h | h⟩ := step
    · exact Or.inr ((Subsingleton.elim j 0) ▸ h.2.symm)
    · exact Or.inl ((Subsingleton.elim j 0) ▸ h.2.symm)

/-- A single sheet over a non-loop edge gives two distinct source vertices. The endpoint map
is a bijection, retaining the incidental choice of ordering of the source edge. -/
theorem shape_of_cover_sum_one (G : FixedGraphSupport T v e) (hs : ∑ j, (G.cover j : ℕ) = 1)
    (hne : ∀ j, (T.edges (G.edgeIndex j)).source ≠ (T.edges (G.edgeIndex j)).target) :
    v = 2 ∧ e = 1 ∧ ∀ j, (G.cover j : ℕ) = 1 ∧ Function.Bijective (G.endpoint j) := by
  obtain rfl := G.edgeCount_of_cover_sum_one hs
  have ends : G.endpoint 0 0 ≠ G.endpoint 0 1 := by
    intro he
    have h := congrArg G.image he
    rcases G.incident 0 with fwd | rev
    · exact hne 0 (fwd.1.symm.trans (h.trans fwd.2))
    · exact hne 0 (rev.2.symm.trans (h.symm.trans rev.1))
  have hinj : Function.Injective (G.endpoint 0) := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact (ends h).elim
    · exact (ends h.symm).elim
    · rfl
  have hsurj : Function.Surjective (G.endpoint 0) := fun m ↦
    (G.vertex_end_of_single m).elim (fun h ↦ ⟨0, h.symm⟩) (fun h ↦ ⟨1, h.symm⟩)
  have hc := Fintype.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  refine ⟨by simpa only [Fintype.card_fin] using hc.symm, rfl, ?_⟩
  intro j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  exact ⟨by simpa only [Fin.sum_univ_one] using hs, hinj, hsurj⟩

end AxiomaticGW.GKM.FixedGraphSupport
