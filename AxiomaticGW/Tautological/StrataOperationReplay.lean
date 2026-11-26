/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.StrataOperation
public import AxiomaticGW.Tautological.RelationCertificate

/-!
# Finite replay of contextual relation images

An incoming destination table is only a lookup hint. Every supported source
column must be isomorphic to its computed image, and exact coefficients are
then added at those verified destinations. In particular a wrong attachment,
node power, label permutation or coefficient cannot be accepted merely by
supplying the same error in an incoming row.
-/

@[expose] public section

namespace AxiomaticGW.StrataOperation
open RelationCertificate

/-- Exact coefficient accumulation along a candidate finite lookup. -/
def imageCoordinates {m n : ℕ} (destination : Fin m → Fin n) (q : Coordinates m) :
    Coordinates n := ∑ i, Pi.single (destination i) (q i)

/-- A bijective destination table acts by inverse reindexing, without a dense sum. -/
theorem imageCoordinates_equiv {n : ℕ} (e : Equiv.Perm (Fin n)) (q : Coordinates n) :
    imageCoordinates e q = fun i ↦ q (e.symm i) := by
  ext j
  simp only [imageCoordinates, Finset.sum_apply]
  rw [Finset.sum_eq_single (e.symm j)]
  · rw [Equiv.apply_symm_apply, Pi.single_eq_same]
  · intro i _ hi
    apply Pi.single_eq_of_ne
    intro he
    exact hi ((congrArg e.symm he).trans (e.symm_apply_apply i)).symm
  · intro hj
    exact (hj (Finset.mem_univ _)).elim

/-- Graph coverage binds the linear image to the verified coordinate accumulation. -/
theorem map_interpret {g₀ g m n : ℕ} {S₀ S : Type} [Fintype S₀] [Fintype S]
    (x : StrataOperation g₀ S₀ g S)
    (source : Fin m → DecoratedStableGraph S₀) (hs : ∀ i, (source i).graph.totalGenus = g₀)
    (target : Fin n → DecoratedStableGraph S) (ht : ∀ i, (target i).graph.totalGenus = g)
    (q : Coordinates m) (destination : Fin m → Fin n)
    (hc : ∀ i, q i ≠ 0 → (x.graph (source i)).isomorphic? (target (destination i)) = true) :
    x.map (interpret (fun i ↦ TautologicalStratum.mk (source i) (hs i)) q) =
      interpret (fun i ↦ TautologicalStratum.mk (target i) (ht i))
        (imageCoordinates destination q) := by
  classical
  rw [interpret_apply, map_sum, imageCoordinates, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_basis]
  simp only [interpret, Fintype.linearCombination_apply_single]
  by_cases hi : q i = 0
  · rw [hi, zero_smul, zero_smul]
  · congr 2
    apply Quotient.sound
    exact (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp (hc i hi)

/-- A verified label permutation transports coordinates by its inverse column permutation. -/
theorem relabel_interpret {g n : ℕ} {S : Type} [Fintype S] (e : S ≃ S)
    (frame : Fin n → DecoratedStableGraph S) (hf : ∀ i, (frame i).graph.totalGenus = g)
    (q : Coordinates n) (d : Equiv.Perm (Fin n))
    (hc : ∀ i, ((frame i).relabel e).isomorphic? (frame (d i)) = true) :
    StrataModule.relabel e (interpret (fun i ↦ TautologicalStratum.mk (frame i) (hf i)) q) =
      interpret (fun i ↦ TautologicalStratum.mk (frame i) (hf i)) (fun i ↦ q (d.symm i)) := by
  let x : StrataOperation g S g S := .relabel e .input
  have h := x.map_interpret frame hf frame hf q d (fun i _ ↦ hc i)
  rw [imageCoordinates_equiv] at h
  simpa only [x, map, LinearMap.comp_apply, LinearMap.id_apply] using h

end AxiomaticGW.StrataOperation
