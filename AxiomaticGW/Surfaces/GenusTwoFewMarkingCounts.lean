/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoFewMarkingDimension

/-! # Counting all three genus-two few-marking benchmarks

At each energy the curve classes have the same allowed marking lists. The fibers
over distinct full classes are disjoint, as are the four positive energy slices.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo

/-- The few-marking suite at a fixed positive curve class consists of its dimension shapes. -/
theorem fewMarkingQueries_filter_class {X : SurfaceTarget} (b : X.Curve)
    (hb : 0 < X.effective.energy b) (h4 : X.effective.energy b ≤ 4) :
    (fewMarkingQueries X).filter (fun q ↦ q.beta = b) =
      (dimensionShapes X (X.effective.energy b)).image (fun m ↦ (⟨2, b, m⟩ : SurfaceQuery X)) := by
  ext q
  rw [Finset.mem_filter, mem_fewMarkingQueries_iff, Finset.mem_image]
  constructor
  · rintro ⟨⟨hg, _, _, hn, hd⟩, hc⟩
    have hq : (⟨2, b, q.insertions⟩ : SurfaceQuery X) = q :=
      (SurfaceQuery.eq_iff _ _).mpr ⟨hg.symm, hc.symm, rfl⟩
    exact ⟨q.insertions, (mem_dimensionShapes_iff b hb _).mpr ⟨hn, hq.symm ▸ hd⟩, hq⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨hn, hd⟩ := (mem_dimensionShapes_iff b hb _).mp hm
    have hne : b ≠ 0 := by
      intro h
      rw [h, map_zero] at hb
      exact Nat.lt_irrefl 0 hb
    exact ⟨⟨rfl, hne, h4, hn, hd⟩, rfl⟩

/-- Count the two-marked lists by their ordered labels and the first cotangent power. -/
theorem card_dimensionShapes (X : SurfaceTarget) (e : ℕ) :
    (dimensionShapes X e).card = Fintype.card (SurfaceBasisLabel X) +
      ∑ a : SurfaceBasisLabel X, ∑ c : SurfaceBasisLabel X,
        (e + 3 - (a.codimension + c.codimension) + 1) := by
  let single := fun a : SurfaceBasisLabel X ↦
    ([⟨a, e + 2 - a.codimension⟩] : List (SurfaceInsertion X))
  let total := fun a c : SurfaceBasisLabel X ↦ e + 3 - (a.codimension + c.codimension)
  let pair := fun (a c : SurfaceBasisLabel X) (k : ℕ) ↦
    ([⟨a, k⟩, ⟨c, total a c - k⟩] : List (SurfaceInsertion X))
  let rows := fun a c ↦ (Finset.range (total a c + 1)).image (pair a c)
  let first := fun a ↦ Finset.univ.biUnion (rows a)
  have disj₁ : Disjoint (Finset.univ.image single) (Finset.univ.biUnion first) := by
    apply Finset.disjoint_left.mpr
    rintro _ hs hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hv
    have hlen := congrArg List.length hk
    change 2 = 1 at hlen
    omega
  have disj₂ : (↑(Finset.univ : Finset (SurfaceBasisLabel X)) : Set _).PairwiseDisjoint first := by
    intro u _ v _ huv
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨d, _, hd⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hd
    exact huv (congrArg SurfaceInsertion.label (List.cons.inj hj).1).symm
  have disj₃ (a) :
      (↑(Finset.univ : Finset (SurfaceBasisLabel X)) : Set _).PairwiseDisjoint (rows a) := by
    intro c _ d _ hcd
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hq
    exact hcd (congrArg SurfaceInsertion.label (List.cons.inj (List.cons.inj hj).2).1).symm
  have single_inj : Function.Injective single :=
    fun _ _ h ↦ congrArg SurfaceInsertion.label (List.cons.inj h).1
  have pair_inj (a c) : Function.Injective (pair a c) :=
    fun _ _ h ↦ congrArg SurfaceInsertion.psi (List.cons.inj h).1
  change ((Finset.univ.image single) ∪ Finset.univ.biUnion first).card = _
  rw [Finset.card_union_of_disjoint disj₁, Finset.card_image_of_injective _ single_inj,
    Finset.card_univ, Finset.card_biUnion disj₂]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change (Finset.univ.biUnion (rows a)).card = _
  rw [Finset.card_biUnion (disj₃ a)]
  apply Finset.sum_congr rfl
  intro c _
  exact (Finset.card_image_of_injective _ (pair_inj a c)).trans (Finset.card_range _)

/-- Count a positive energy slice by full curve class and ordered marking list. -/
theorem card_fewMarkingsAtEnergy (X : SurfaceTarget) (e : ℕ) (h : e ∈ Finset.Icc 1 4) :
    (fewMarkingsAtEnergy X e).card =
      ((X.bounded e).filter (fun b ↦ X.effective.energy b = e)).card *
        (dimensionShapes X e).card := by
  have he := Finset.mem_Icc.mp h
  have inj (b : X.Curve) : Function.Injective (fun m ↦ (⟨2, b, m⟩ : SurfaceQuery X)) :=
    fun _ _ hEq ↦ congrArg SurfaceQuery.insertions hEq
  rw [fewMarkingsAtEnergy_eq_shapes X e he.1 he.2, Finset.card_biUnion]
  · simp only [Finset.card_image_of_injective _ (inj _), Finset.sum_const, nsmul_eq_mul,
      Nat.cast_id]
  · intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hq'
    exact hbc (congrArg SurfaceQuery.beta hEq).symm

/-- Disjoint energy counts give the size of the original benchmark. -/
theorem card_fewMarkingQueries (X : SurfaceTarget) :
    (fewMarkingQueries X).card = ∑ e ∈ Finset.Icc 1 4,
      ((X.bounded e).filter (fun b ↦ X.effective.energy b = e)).card *
        (dimensionShapes X e).card := by
  have decomp : fewMarkingQueries X = (Finset.Icc 1 4).biUnion (fewMarkingsAtEnergy X) := by
    ext q
    rw [mem_fewMarkingQueries_iff, Finset.mem_biUnion]
    constructor
    · intro h
      have hn : X.effective.energy q.beta ≠ 0 :=
        fun hz ↦ h.2.1 ((X.effective.energy_eq_zero_iff _).mp hz)
      exact ⟨_, Finset.mem_Icc.mpr ⟨by omega, h.2.2.1⟩,
        (mem_fewMarkingsAtEnergy_iff _ _).mpr ⟨h, rfl⟩⟩
    · rintro ⟨e, _, he⟩
      exact ((mem_fewMarkingsAtEnergy_iff q e).mp he).1
  rw [decomp, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun e he ↦ card_fewMarkingsAtEnergy X e he
  · intro e _ f _ hef
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    exact hef (((mem_fewMarkingsAtEnergy_iff q e).mp hq).2.symm.trans
      ((mem_fewMarkingsAtEnergy_iff q f).mp hq').2)

/-- The complete ordered genus-two suites contain 48, 656 and 4,495 queries, respectively. -/
theorem benchmark_sizes :
    (fewMarkingQueries .plane).card = 48 ∧
    (fewMarkingQueries .hirzebruchOne).card = 656 ∧
    (fewMarkingQueries .blowupTwo).card = 4495 := by
  simp only [card_fewMarkingQueries, card_dimensionShapes]
  decide +kernel

end AxiomaticGW.SurfaceGenusTwo
