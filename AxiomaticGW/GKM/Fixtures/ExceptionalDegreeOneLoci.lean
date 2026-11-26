/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.SingleCoveredEdge
public import AxiomaticGW.GKM.Fixtures.ExceptionalAxisTransport

/-! # Degree-one exceptional genus-two supports with one labeled marking

A single unramified edge joins distinct fixed points, so its connected source graph is a
tree. Order its endpoints by the pinned target edge, independently of source labels and the
input edge orientation. Distributing genus two and choosing the marked endpoint gives six
possibilities before the localization integrand's dimension test.
-/

public section
namespace AxiomaticGW.GKM.ExceptionalDegreeOneLoci
open CurveReplay.TwoBlowups (tables)
open ExceptionalAxisTransport (twoBlowups_class_iff)

/-- The source genus and the marked end (0 source, 1 target) of the unique exceptional edge. -/
abbrev Index := Fin 3 × Fin 2

/-- The actual index, ordered cones, first character and normal degree in the pinned table. -/
theorem fixed_frame : let t := tables.edges 2
    t.source = 1 ∧ t.target = 2 ∧ tables.points t.source = ![0, 3] ∧
    tables.points t.target = ![1, 3] ∧ t.curve = ![1, 0, 0] ∧ t.weight = ![1, -1] ∧
    t.normalDegree = -1 := by decide +kernel

variable {v e : ℕ} (G : FixedGraphSupport tables v e) (hd : G.degree = ![1, 0, 0])

section
include hd

/-- Complete shape and covering degree for any connected source of the packet's full class. -/
theorem source_shape : v = 2 ∧ e = 1 ∧ ∀ j, G.edgeIndex j = 2 ∧ (G.cover j : ℕ) = 1 ∧
    Function.Bijective (G.endpoint j) := by
  have hclass : G.degree = (1 : ℕ) • SurfaceTarget.blowupTwo.exceptionalCurve 0 :=
    hd.trans (by decide +kernel)
  obtain ⟨ht, hs⟩ := (twoBlowups_class_iff 0 1 G).mp hclass
  have t (j : Fin e) : G.edgeIndex j = 2 := (ht j).trans (by decide +kernel)
  obtain ⟨hv, he, h⟩ := G.shape_of_cover_sum_one hs (fun j ↦ by rw [t]; decide +kernel)
  exact ⟨hv, he, fun j ↦ ⟨t j, h j⟩⟩

/-- Target images canonically distinguish the two vertices, including a reversed input edge. -/
theorem unique_ends : ∃! k : Fin 2 ≃ Fin v, ∀ p, G.image (k p) = ![1, 2] p := by
  obtain ⟨_, he, h⟩ := source_shape G hd
  subst e
  let raw := Equiv.ofBijective (G.endpoint 0) (h 0).2.2
  have inc := G.incident 0
  rw [(h 0).1] at inc
  have existsEnds : ∃ k : Fin 2 ≃ Fin v, ∀ p, G.image (k p) = ![1, 2] p := by
    rcases inc with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · refine ⟨raw, ?_⟩
      intro p
      fin_cases p
      · exact hl
      · exact hr
    · refine ⟨(Equiv.swap 0 1).trans raw, ?_⟩
      intro p
      fin_cases p
      · change G.image (raw ((Equiv.swap (0 : Fin 2) 1) 0)) = 1
        rw [Equiv.swap_apply_left]
        exact hr
      · change G.image (raw ((Equiv.swap (0 : Fin 2) 1) 1)) = 2
        rw [Equiv.swap_apply_right]
        exact hl
  obtain ⟨k, hk⟩ := existsEnds
  have hi : Function.Injective G.image := by
    intro a b hab
    obtain ⟨p, rfl⟩ := k.surjective a
    obtain ⟨q, rfl⟩ := k.surjective b
    rw [hk, hk] at hab
    have inj : Function.Injective (![1, 2] : Fin 2 → Fin 5) := by decide +kernel
    exact congrArg k (inj hab)
  refine ⟨k, hk, ?_⟩
  intro k' hk'
  exact Equiv.ext fun p ↦ hi ((hk' p).trans (hk p).symm)

/-- The native order determined by the fixed-point images rather than any source-edge labels. -/
noncomputable def ends : Fin 2 ≃ Fin v := (unique_ends G hd).exists.choose

/-- Fixed-point images of the canonically ordered source vertices. -/
theorem ends_image (p : Fin 2) : G.image (ends G hd p) = ![1, 2] p :=
  (unique_ends G hd).exists.choose_spec p

/-- Any permutation of the source vertices preserving the target labels fixes every vertex. -/
theorem vertex_automorphism (σ : Fin v ≃ Fin v) (hσ : ∀ w, G.image (σ w) = G.image w) :
    σ = Equiv.refl _ := by
  have h : (ends G hd).trans σ = ends G hd :=
    (unique_ends G hd).unique (fun p ↦ (hσ _).trans (ends_image G hd p)) (ends_image G hd)
  apply Equiv.ext
  intro w
  obtain ⟨p, rfl⟩ := (ends G hd).surjective w
  exact DFunLike.congr_fun h p

end

/-- The two vertex genera of a canonical index. -/
@[expose] def genera (k : Index) : Fin 2 → ℕ := ![k.1.val, 2 - k.1.val]

/-- Genus assignments and the labeled mark subject to the connected arithmetic genus formula. -/
abbrev Decoration (v e : ℕ) :=
  {z : (Fin v → ℕ) × Fin v // (∑ w, z.1 w) + (e + 1 - v) = 2}

section
include hd

private theorem genus_pair (z : Decoration v e) :
    z.val.1 (ends G hd 0) + z.val.1 (ends G hd 1) = 2 := by
  obtain ⟨hv, he, _⟩ := source_shape G hd
  have hh := z.property
  have rearranged := (ends G hd).sum_comp z.val.1
  rw [Fin.sum_univ_two] at rearranged
  exact rearranged.trans (by omega)

/-- Bijection for any representative. It keeps precisely the source genus and the marked
endpoint. The target genus is recovered by subtraction because the graph is a tree. -/
noncomputable def decorationEquiv : Decoration v e ≃ Index where
  toFun z :=
    (⟨z.val.1 (ends G hd 0), by have := genus_pair G hd z; omega⟩, (ends G hd).symm z.val.2)
  invFun k := ⟨(fun w ↦ genera k ((ends G hd).symm w), ends G hd k.2), by
    obtain ⟨hv, he, _⟩ := source_shape G hd
    rw [show e + 1 - v = 0 by omega, Nat.add_zero]
    rw [← (ends G hd).sum_comp, Fin.sum_univ_two]
    simp only [Equiv.symm_apply_apply, genera, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · funext w
      obtain ⟨p, rfl⟩ := (ends G hd).surjective w
      simp only [Equiv.symm_apply_apply]
      fin_cases p
      · rfl
      · change 2 - z.val.1 (ends G hd 0) = z.val.1 (ends G hd 1)
        have := genus_pair G hd z
        omega
    · exact (ends G hd).apply_symm_apply _
  right_inv k := by
    apply Prod.ext
    · apply Fin.ext
      change genera k ((ends G hd).symm (ends G hd 0)) = k.1.val
      rw [Equiv.symm_apply_apply]
      rfl
    · exact (ends G hd).symm_apply_apply _

/-- The indexing convention is fixed by the original vertex genus and marked-point image. -/
theorem index_binding (z : Decoration v e) :
    let k := decorationEquiv G hd z
    (∀ p, z.val.1 (ends G hd p) = genera k p) ∧ ends G hd k.2 = z.val.2 := by
  constructor
  · intro p
    fin_cases p
    · rfl
    · change z.val.1 (ends G hd 1) = 2 - z.val.1 (ends G hd 0)
      have := genus_pair G hd z
      omega
  · exact (ends G hd).apply_symm_apply _

/-- Every representative has exactly six genus/mark decorations under this fixed normalization. -/
theorem six_decorations : Nat.card (Decoration v e) = 6 := by
  rw [Nat.card_congr (decorationEquiv G hd), Nat.card_eq_fintype_card]
  decide +kernel

end

/-- The degree-one single-cover representative exists for every canonical index. -/
theorem all_realized (k : Index) : let G := FixedGraphSupport.singleCover tables 2 1 false
    ∃ z : Decoration 2 1,
      decorationEquiv G (by rw [FixedGraphSupport.degree_singleCover]; decide) z = k :=
  (decorationEquiv _ _).surjective k

/-- At the marked endpoint there is one marking and one flag. The stable-vertex dimension
cut for ψ³ removes exactly the two indices with split genus `(1,1)`. -/
theorem stable_dimension_cut : ∀ k : Index,
    (0 < genera k k.2 ∧ 3 * genera k k.2 - 3 + 2 < 3) ↔ k.1 = 1 := by decide +kernel

end AxiomaticGW.GKM.ExceptionalDegreeOneLoci
