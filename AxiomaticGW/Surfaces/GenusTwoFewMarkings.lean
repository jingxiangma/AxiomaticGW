/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Queries

/-!
# Complete few-marking genus-two request domains for the three fixed surfaces

The acceptance domain has positive effective class, anticanonical energy at
most four, at most two ordered basis insertions, and the signed virtual
dimension equation. These conditions imply that every psi power is at most
seven. The executable frame retains all curve coordinates, exceptional labels
and ordered state/power pairs. It contains no proposed invariant values.

The plane has a smaller existing enumeration using its forced degree one.
Both enumerate the same mathematical domain; the plane comparison is tested
without changing that established request list.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo

/-- The unchanged few-marking benchmark contract for any fixed target. -/
def FewMarkingQuery {X : SurfaceTarget} (q : SurfaceQuery X) : Prop :=
  q.genus = 2 ∧ q.beta ≠ 0 ∧ X.effective.energy q.beta ≤ 4 ∧
    q.insertions.length ≤ 2 ∧ q.DimensionCompatible

/-- Enumerate the ordered markings at one fixed curve class in the benchmark. -/
def fewMarkingsAtClass (X : SurfaceTarget) (beta : X.Curve) : Finset (SurfaceQuery X) :=
  Finset.univ.biUnion fun n : Fin 3 ↦
      Finset.univ.biUnion fun a : Fin n.val → SurfaceBasisLabel X ↦
        (Finset.univ.filter fun k : Fin n.val → Fin 8 ↦
          SurfaceQuery.DimensionCompatible
            (⟨2, beta, List.ofFn (fun i ↦ ⟨a i, (k i).val⟩)⟩ : SurfaceQuery X)).image fun k ↦
          (⟨2, beta, List.ofFn (fun i ↦ ⟨a i, (k i).val⟩)⟩ : SurfaceQuery X)

/-- Enumerate the complete benchmark using full effective curve coordinates. -/
def fewMarkingQueries (X : SurfaceTarget) : Finset (SurfaceQuery X) :=
  ((X.bounded 4).filter (fun beta ↦ beta ≠ 0)).biUnion (fewMarkingsAtClass X)

/-- The original benchmark restricted to a single anticanonical energy. -/
def fewMarkingsAtEnergy (X : SurfaceTarget) (e : ℕ) : Finset (SurfaceQuery X) :=
  ((X.bounded 4).filter (fun beta ↦ beta ≠ 0 ∧ X.effective.energy beta = e)).biUnion
    (fewMarkingsAtClass X)

private theorem beta_of_mem_atClass {X : SurfaceTarget} {beta : X.Curve} {q : SurfaceQuery X}
    (h : q ∈ fewMarkingsAtClass X beta) : q.beta = beta := by
  obtain ⟨_, _, h⟩ := Finset.mem_biUnion.mp h
  obtain ⟨_, _, h⟩ := Finset.mem_biUnion.mp h
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h
  rfl

/-- The power bound follows from the benchmark, independently of the enumeration. -/
theorem FewMarkingQuery.psi_lt_eight {X : SurfaceTarget} {q : SurfaceQuery X}
    (h : FewMarkingQuery q) (i : Fin q.insertions.length) : (q.insertions.get i).psi < 8 := by
  obtain ⟨hg, _, he, hn, hd⟩ := h
  change (q.totalCodimension : ℤ) =
    (X.effective.energy q.beta : ℤ) + (q.genus : ℤ) - 1 + q.insertions.length at hd
  rw [hg] at hd
  have hi : (q.insertions.get i).label.codimension + (q.insertions.get i).psi ≤
      q.totalCodimension := by
    unfold SurfaceQuery.totalCodimension
    exact Finset.single_le_sum (f := fun j : Fin q.insertions.length ↦
      (q.insertions.get j).label.codimension + (q.insertions.get j).psi)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- Completeness is against the original dimension and energy conditions,
not a supplied list or a collection of expected numerical answers. -/
theorem mem_fewMarkingQueries_iff {X : SurfaceTarget} (q : SurfaceQuery X) :
    q ∈ fewMarkingQueries X ↔ FewMarkingQuery q := by
  constructor
  · intro h
    obtain ⟨beta, hb, hn⟩ := Finset.mem_biUnion.mp h
    obtain ⟨n, _, ha⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨a, _, hk⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨k, hk_mem, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨he, hnz⟩ := Finset.mem_filter.mp hb
    rw [X.bounded_eq, X.effective.mem_bounded] at he
    refine ⟨rfl, hnz, he, ?_, (Finset.mem_filter.mp hk_mem).2⟩
    simp only [List.length_ofFn]
    omega
  · intro h
    have hp := h.psi_lt_eight
    obtain ⟨hg, hnz, he, hn, hd⟩ := h
    let n : Fin 3 := ⟨q.insertions.length, by omega⟩
    let a : Fin n.val → SurfaceBasisLabel X := fun i ↦ (q.insertions.get i).label
    let k : Fin n.val → Fin 8 := fun i ↦ ⟨(q.insertions.get i).psi, hp i⟩
    have hq : (⟨2, q.beta, List.ofFn (fun i ↦ ⟨a i, (k i).val⟩)⟩ : SurfaceQuery X) = q := by
      apply (SurfaceQuery.eq_iff _ _).mpr
      refine ⟨hg.symm, rfl, ?_⟩
      change List.ofFn (fun i : Fin q.insertions.length ↦ q.insertions.get i) = q.insertions
      exact List.ofFn_get q.insertions
    apply Finset.mem_biUnion.mpr
    refine ⟨q.beta, Finset.mem_filter.mpr ⟨?_, hnz⟩, ?_⟩
    · rw [X.bounded_eq, X.effective.mem_bounded]
      exact he
    · apply Finset.mem_biUnion.mpr
      refine ⟨n, Finset.mem_univ _, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨a, Finset.mem_univ _, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hq⟩
      rwa [hq]

/-- Membership retains all the defining conditions of the original benchmark. -/
theorem mem_fewMarkingsAtEnergy_iff {X : SurfaceTarget} (q : SurfaceQuery X) (e : ℕ) :
    q ∈ fewMarkingsAtEnergy X e ↔ FewMarkingQuery q ∧ X.effective.energy q.beta = e := by
  rw [← mem_fewMarkingQueries_iff q]
  constructor
  · intro h
    obtain ⟨b, hb, hq⟩ := Finset.mem_biUnion.mp h
    obtain ⟨hb, hn, he⟩ := Finset.mem_filter.mp hb
    exact ⟨Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hn⟩, hq⟩,
      (congrArg X.effective.energy (beta_of_mem_atClass hq)).trans he⟩
  · rintro ⟨h, he⟩
    obtain ⟨b, hb, hq⟩ := Finset.mem_biUnion.mp h
    obtain ⟨hb, hn⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr
      ⟨hb, hn, (congrArg X.effective.energy (beta_of_mem_atClass hq)).symm.trans he⟩, hq⟩

/-- No positive-class empty request satisfies the genus-two dimension equation. -/
theorem FewMarkingQuery.insertions_ne_nil {X : SurfaceTarget} {q : SurfaceQuery X}
    (h : FewMarkingQuery q) : q.insertions ≠ [] := by
  intro hempty
  have hzero : q.totalCodimension = 0 := by
    unfold SurfaceQuery.totalCodimension
    apply Finset.sum_eq_zero
    intro i _
    have hi := i.isLt
    have hn : q.insertions.length = 0 := congrArg List.length hempty
    omega
  have hd := h.2.2.2.2
  change (q.totalCodimension : ℤ) =
    (X.effective.energy q.beta : ℤ) + (q.genus : ℤ) - 1 + q.insertions.length at hd
  rw [hzero, h.1, hempty] at hd
  omega

end AxiomaticGW.SurfaceGenusTwo
