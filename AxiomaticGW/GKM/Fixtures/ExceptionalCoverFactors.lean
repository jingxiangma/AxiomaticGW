/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalCharacterField

/-! # Multiple-cover edge factors on the exceptional curves

For the normal line of degree −1, the native b-function is the product of the
interior weights on the interval between the two normal characters. The cover
automorphism factor is separate from this deformation and obstruction factor.
-/

@[expose] public section
namespace AxiomaticGW.GKM.ExceptionalCoverFactors
open EquivariantCoefficients CurveConventionCertificate ExceptionalAxisTransport
open ExceptionalCharacterField
open CurveReplay.OneBlowup renaming tables → f1
open CurveReplay.TwoBlowups renaming tables → bl2
noncomputable section

/-- The negative-degree b-function at a d-fold cover, with indices 1 through d−1. -/
def normal (d : ℕ+) (w n : Coefficient) : Coefficient :=
  ∏ j : Fin (d.val - 1), (n + (j.val + 1 : Coefficient) * (w / d.val))

/-- Native edge deformation and normal obstruction, before division by automorphisms. -/
def factor (d : ℕ+) (w n : Coefficient) : Coefficient :=
  (-1) ^ d.val / (d.val.factorial : Coefficient)^2 / (w / d.val)^(2*d.val) * normal d w n

/-- Reversing a cover swaps its end characters and reverses the interior-weight indices. -/
theorem reverse (d : ℕ+) (w n : Coefficient) :
    factor d (-w) (n + w) = factor d w n := by
  have hd : (d.val : Coefficient) ≠ 0 := Nat.cast_ne_zero.mpr d.ne_zero
  have hn : normal d (-w) (n + w) = normal d w n := by
    unfold normal
    rw [← Equiv.prod_comp Fin.revPerm (fun j : Fin (d.val - 1) ↦
      n + (j.val + 1 : Coefficient) * (w / d.val))]
    apply Finset.prod_congr rfl
    intro j _
    have hj : j.val + 1 + ((Fin.revPerm j).val + 1) = d.val := by
      change j.val + 1 + ((d.val - 1 - (j.val + 1)) + 1) = d.val
      omega
    have hc : (j.val : Coefficient) + 1 + (((Fin.revPerm j).val : Coefficient) + 1) = d.val := by
      exact_mod_cast hj
    field_simp
    linear_combination -w * hc
  rw [factor, hn, factor, neg_div, pow_mul, neg_sq, ← pow_mul]

/-- Exact field transport for all sheets, including the entire normal-weight product. -/
theorem map_factor (φ : Coefficient ≃+* Coefficient) (d : ℕ+) (w n : Coefficient) :
    φ (factor d w n) = factor d (φ w) (φ n) := by
  simp only [factor, normal, map_mul, map_div₀, map_pow, map_neg, map_one, map_natCast,
    map_prod, map_add]

/-- The positive tangent and transverse normal in the oriented exceptional edge table. -/
def atEdge {X : SurfaceTarget} {v e : ℕ} (t : Tables X v e) (k : Fin e) (d : ℕ+) :
    Coefficient :=
  let a := t.edges k
  factor d (character a.weight) (character (edgeWeight t a.source a.normalSource))

/-- Each genuine exceptional edge has a nonzero tangent denominator in every cover degree. -/
theorem tangent_ne_zero (i : Fin 2) (d : ℕ+) :
    character (f1.edges 2).weight / d.val ≠ 0 ∧
    character (bl2.edges (exceptionalEdge i)).weight / d.val ≠ 0 := by
  have hd : (d.val : Coefficient) ≠ 0 := Nat.cast_ne_zero.mpr d.ne_zero
  have hw : character (f1.edges 2).weight = x-y := by
    change ((1 : ℤ) : Coefficient)*x + ((-1 : ℤ) : Coefficient)*y = x-y
    push_cast
    ring
  have h : character (f1.edges 2).weight ≠ 0 := hw ▸ x_sub_y_ne_zero
  rw [← (local_field_weights i).1]
  exact ⟨div_ne_zero h hd, div_ne_zero ((map_ne_zero_iff _ (sector i).injective).mpr h) hd⟩

/-- Both complete multiple-cover edge factors come from the pinned normal bundle of degree −1. -/
theorem transport (i : Fin 2) (d : ℕ+) :
    (f1.edges 2).normalDegree = -1 ∧ (bl2.edges (exceptionalEdge i)).normalDegree = -1 ∧
    sector i (atEdge f1 2 d) = atEdge bl2 (exceptionalEdge i) d := by
  obtain ⟨_, h₁, h₂, _⟩ := local_weights i
  exact ⟨h₁, h₂, by rw [atEdge, atEdge, map_factor, (local_field_weights i).1,
    (local_field_weights i).2.1]⟩

/-- At the opposite endpoint the native normal gains the primitive tangent character. -/
theorem opposite_normal (i : Fin 2) :
    let a := f1.edges 2; let b := bl2.edges (exceptionalEdge i)
    character (edgeWeight f1 a.target a.normalTarget) =
      character (edgeWeight f1 a.source a.normalSource) + character a.weight ∧
    character (edgeWeight bl2 b.target b.normalTarget) =
      character (edgeWeight bl2 b.source b.normalSource) + character b.weight := by
  have add (u v : Fin 2 → ℤ) : character (u + v) = character u + character v := by
    simp only [character, Pi.add_apply, Int.cast_add, add_mul]
    ring
  have h : let a := f1.edges 2
      edgeWeight f1 a.target a.normalTarget = edgeWeight f1 a.source a.normalSource + a.weight := by
    decide +kernel
  have hn := (congrArg character h).trans (add _ _)
  refine ⟨hn, ?_⟩
  obtain ⟨hw, hs, ht, _⟩ := local_field_weights i
  rw [← ht, ← hs, ← hw, hn, map_add]

/-- A genus-zero fixed graph consisting of the single unmarked cover has two unstable ends.
Their source factors cancel the tangent normalizations and leave two oriented flags. Division
by the deck-group order gives this individual graph's contribution. -/
theorem unmarked_cover (d : ℕ+) (w n : Coefficient) (hw : w ≠ 0) (hn : n ≠ 0)
    (ht : n + w ≠ 0) :
    factor d w n * ((w*n) * ((-w)*(n+w))) *
      (((w/d.val)/(w*n)) * (((-w)/d.val)/((-w)*(n+w)))) / d.val =
      -(w/d.val)^2 * factor d w n / d.val := by
  have hd : (d.val : Coefficient) ≠ 0 := Nat.cast_ne_zero.mpr d.ne_zero
  field_simp

/-- The native tangent normalization at a vertex of the indicated valence. -/
def tangent {X : SurfaceTarget} {v e : ℕ} (t : Tables X v e) (p : Fin v) (valence : ℕ) :
    Coefficient := ∏ j, character (t.tangent p j)^valence

/-- The two tangent directions are swapped at the target end; their product is preserved. -/
theorem endpoint_tangents (i : Fin 2) (valence : ℕ) :
    let a := f1.edges 2; let b := bl2.edges (exceptionalEdge i)
    sector i (tangent f1 a.source valence) = tangent bl2 b.source valence ∧
    sector i (tangent f1 a.target valence) = tangent bl2 b.target valence := by
  have ht := (local_field_weights i).2.2.2
  simp only [tangent, Fin.prod_univ_two, map_mul, map_pow, (ht 0).1, (ht 1).1, (ht 0).2, (ht 1).2]
  exact ⟨trivial, mul_comm _ _⟩

/-- On every connected exceptional support, the product of the factors of its individual
edges transports, retaining parallel edges and their actual covering multiplicities. -/
theorem graph_product (i : Fin 2) (d : ℕ+) {v e : ℕ}
    (g : {G : FixedGraphSupport f1 v e //
      G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0}) :
    let h := (ofSizeEquiv i d v e g).val
    sector i (∏ a, atEdge f1 (g.val.edgeIndex a) (g.val.cover a)) =
      ∏ a, atEdge bl2 (h.edgeIndex a) (h.cover a) := by
  have hz : g.val.degree 1 = 0 := by rw [g.property]; rfl
  have unique : ∀ t : Fin 4, (f1.edges t).curve 1 = 0 → t = 2 := by decide +kernel
  obtain ⟨_, cover, edge⟩ := preserves_covers i d g
  dsimp only
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro a _
  rw [unique _ (g.val.edge_coordinate_zero 1 hz a), cover, edge]
  exact (transport i _).2.2

/-- All vertex normalizations transport for the same incident flags on the source graph. -/
theorem graph_tangent_product (i : Fin 2) (d : ℕ+) {v e : ℕ}
    (g : {G : FixedGraphSupport f1 v e //
      G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0}) :
    let h := (ofSizeEquiv i d v e g).val
    let val := fun (ends : Fin e → Fin 2 → Fin v) p ↦
      (Finset.univ.filter (fun f : Fin e × Fin 2 ↦ ends f.1 f.2 = p)).card
    sector i (∏ p, tangent f1 (g.val.image p) (val g.val.endpoint p)) =
      ∏ p, tangent bl2 (h.image p) (val h.endpoint p) := by
  dsimp only
  rw [map_prod, (preserves_covers i d g).1]
  apply Finset.prod_congr rfl
  intro p _
  rw [vertex_image i d g p]
  rcases oneBlowup_vertices d g.val g.property p with hs | ht
  · rw [hs, if_pos rfl]
    exact (endpoint_tangents i _).1
  · rw [ht, if_neg (by decide +kernel)]
    exact (endpoint_tangents i _).2

end
end AxiomaticGW.GKM.ExceptionalCoverFactors
