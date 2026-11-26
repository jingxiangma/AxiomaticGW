/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Queries

/-!
# Complete plane genus-two few-marking benchmark frame

Positive anticanonical energy at most four forces plane degree one. For at
most two markings the dimension equation bounds every psi power by six.
The finite frame retains ordered state/power occurrences. Its completeness
is proved against the original geometric benchmark predicate, independently
of incoming numerical values or certificate request lists.
-/

@[expose] public section

set_option Elab.async false

namespace AxiomaticGW.BelorousskiPandharipande

/-- The fixed few-marking acceptance domain, stated without enumerator choices. -/
def PlaneFewMarkingQuery (q : SurfaceQuery .plane) : Prop :=
  q.genus = 2 ∧ q.beta ≠ 0 ∧ SurfaceTarget.plane.effective.energy q.beta ≤ 4 ∧
    q.insertions.length ≤ 2 ∧ q.DimensionCompatible

/-- Complete ordered candidates filtered by the signed virtual dimension. -/
def planeFewMarkingQueries : Finset (SurfaceQuery .plane) :=
  Finset.univ.biUnion fun n : Fin 3 ↦
    Finset.univ.biUnion fun a : Fin n.val → SurfaceBasisLabel .plane ↦
      (Finset.univ.filter fun k : Fin n.val → Fin 7 ↦
        SurfaceQuery.DimensionCompatible
          (⟨2, ![1], List.ofFn (fun i ↦ ⟨a i, (k i).val⟩)⟩ : SurfaceQuery .plane)).image fun k ↦
        (⟨2, ![1], List.ofFn (fun i ↦ ⟨a i, (k i).val⟩)⟩ : SurfaceQuery .plane)

/-- Every valid benchmark query occurs, with its full ordered insertion list. -/
theorem mem_planeFewMarkingQueries_iff (q : SurfaceQuery .plane) :
    q ∈ planeFewMarkingQueries ↔ PlaneFewMarkingQuery q := by
  constructor
  · intro h
    obtain ⟨n, _, ha⟩ := Finset.mem_biUnion.mp h
    obtain ⟨a, _, hk⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨k, hk_mem, rfl⟩ := Finset.mem_image.mp hk
    have hd := (Finset.mem_filter.mp hk_mem).2
    refine ⟨rfl, ?_, ?_, ?_, hd⟩
    · change (![1] : SurfaceTarget.plane.Curve) ≠ 0
      decide
    · change SurfaceTarget.plane.effective.energy ![1] ≤ 4
      decide
    · simp only [List.length_ofFn]
      omega
  · rintro ⟨hg, hnz, he, hn, hd⟩
    have hdegree : q.beta 0 = 1 := by
      have hne : q.beta 0 ≠ 0 := by
        intro hz
        apply hnz
        funext i
        fin_cases i
        exact hz
      change (∑ i : Fin 1, (![3] : Fin 1 → ℕ) i * q.beta i) ≤ 4 at he
      rw [Fin.sum_univ_one, Matrix.cons_val_zero] at he
      omega
    have hb : q.beta = ![1] := by
      funext i
      fin_cases i
      exact hdegree
    have hcodim : q.totalCodimension ≤ 6 := by
      change (q.totalCodimension : ℤ) =
        SurfaceTarget.plane.c1Degree q.beta + (q.genus : ℤ) - 1 + q.insertions.length at hd
      rw [hb, hg, show SurfaceTarget.plane.c1Degree ![1] = (3 : ℤ) by decide] at hd
      omega
    have hpower (i : Fin q.insertions.length) : (q.insertions.get i).psi < 7 := by
      have hi : (q.insertions.get i).label.codimension + (q.insertions.get i).psi ≤
          q.totalCodimension := by
        unfold SurfaceQuery.totalCodimension
        exact Finset.single_le_sum (f := fun j : Fin q.insertions.length ↦
          (q.insertions.get j).label.codimension + (q.insertions.get j).psi)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      omega
    let n : Fin 3 := ⟨q.insertions.length, by omega⟩
    let a : Fin n.val → SurfaceBasisLabel .plane := fun i ↦ (q.insertions.get i).label
    let k : Fin n.val → Fin 7 := fun i ↦ ⟨(q.insertions.get i).psi, hpower i⟩
    have hq : (⟨2, ![1], List.ofFn (fun i ↦ ⟨a i, (k i).val⟩)⟩ : SurfaceQuery .plane) = q := by
      apply (SurfaceQuery.eq_iff _ _).mpr
      refine ⟨hg.symm, hb.symm, ?_⟩
      change List.ofFn (fun i : Fin q.insertions.length ↦ q.insertions.get i) = q.insertions
      exact List.ofFn_get q.insertions
    apply Finset.mem_biUnion.mpr
    refine ⟨n, Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hq⟩
    rwa [hq]

set_option maxRecDepth 20000 in
/-- The complete frame has forty-eight ordered requests. -/
theorem planeFewMarkingQueries_card : planeFewMarkingQueries.card = 48 := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- The complete frame includes every arity in the acceptance contract. -/
theorem planeFewMarkingQueries_card_by_arity : ∀ n : Fin 3,
    (planeFewMarkingQueries.filter (fun q ↦ q.insertions.length = n.val)).card =
      (![0, 3, 45] : Fin 3 → ℕ) n := by
  decide +kernel

end AxiomaticGW.BelorousskiPandharipande
