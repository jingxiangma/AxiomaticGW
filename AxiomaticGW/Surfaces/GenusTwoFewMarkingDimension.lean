/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoFewMarkings

/-! # Solving the genus-two virtual dimension condition at one and two markings

At fixed positive energy the first descendant power determines the second. The resulting
enumeration avoids forming pairs of powers that will be discarded on dimension grounds.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
variable {X : SurfaceTarget}

private theorem codim_bound (a : SurfaceBasisLabel X) : a.codimension ≤ 2 := by
  cases a <;> simp only [SurfaceBasisLabel.codimension] <;> omega

private theorem one_weight (b : X.Curve) (a : SurfaceBasisLabel X) (k : ℕ) :
    (⟨2, b, [⟨a, k⟩]⟩ : SurfaceQuery X).DimensionCompatible ↔
      a.codimension + k = X.effective.energy b + 2 := by
  change (↑((∑ j : Fin 1, _) : ℕ) : ℤ) = (↑(X.effective.energy b) : ℤ) + 2 - 1 + 1 ↔ _
  rw [Fin.sum_univ_one]
  change (↑(a.codimension + k) : ℤ) = _ ↔ _
  omega

private theorem two_weight (b : X.Curve) (a c : SurfaceBasisLabel X) (k l : ℕ) :
    (⟨2, b, [⟨a, k⟩, ⟨c, l⟩]⟩ : SurfaceQuery X).DimensionCompatible ↔
      a.codimension + k + (c.codimension + l) = X.effective.energy b + 3 := by
  change (↑((∑ j : Fin 2, _) : ℕ) : ℤ) = (↑(X.effective.energy b) : ℤ) + 2 - 1 + 2 ↔ _
  rw [Fin.sum_univ_two]
  change (↑(a.codimension + k + (c.codimension + l)) : ℤ) = _ ↔ _
  omega

/-- Allowed ordered insertions at one or two markings and the specified energy. -/
def dimensionShapes (X : SurfaceTarget) (e : ℕ) : Finset (List (SurfaceInsertion X)) :=
  (Finset.univ.image fun a : SurfaceBasisLabel X ↦ [⟨a, e + 2 - a.codimension⟩]) ∪
    Finset.univ.biUnion fun a : SurfaceBasisLabel X ↦
      Finset.univ.biUnion fun c : SurfaceBasisLabel X ↦
        let t := e + 3 - (a.codimension + c.codimension)
        (Finset.range (t + 1)).image fun k ↦ [⟨a, k⟩, ⟨c, t - k⟩]

/-- At positive degree these are exactly the lists satisfying the virtual dimension equation. -/
theorem mem_dimensionShapes_iff (b : X.Curve) (hb : 0 < X.effective.energy b)
    (m : List (SurfaceInsertion X)) :
    m ∈ dimensionShapes X (X.effective.energy b) ↔ m.length ≤ 2 ∧
      (⟨2, b, m⟩ : SurfaceQuery X).DimensionCompatible := by
  simp only [dimensionShapes, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, c, k, hk, rfl⟩)
    · refine ⟨Nat.le_succ 1, (one_weight ..).mpr ?_⟩
      have := codim_bound a
      omega
    · refine ⟨le_rfl, (two_weight ..).mpr ?_⟩
      have := codim_bound a
      have := codim_bound c
      omega
  · rintro ⟨hn, hw⟩
    obtain _ | ⟨⟨a, k⟩, rest⟩ := m
    · change (↑((∑ j : Fin 0, _) : ℕ) : ℤ) = (↑(X.effective.energy b) : ℤ) + 2 - 1 + 0 at hw
      rw [Fin.sum_univ_zero] at hw
      omega
    obtain _ | ⟨⟨c, l⟩, rest⟩ := rest
    · have h := (one_weight b a k).mp hw
      exact Or.inl ⟨a, by rw [show X.effective.energy b + 2 - a.codimension = k by omega]⟩
    obtain _ | ⟨s, tail⟩ := rest
    · have h := (two_weight b a c k l).mp hw
      refine Or.inr ⟨a, c, k, by omega, ?_⟩
      rw [show X.effective.energy b + 3 - (a.codimension + c.codimension) - k = l by omega]
    · simp only [List.length_cons] at hn
      omega

/-- Compute the original energy slice by solving for the final cotangent power. -/
theorem fewMarkingsAtEnergy_eq_shapes (X : SurfaceTarget) (e : ℕ) (he : 0 < e) (h4 : e ≤ 4) :
    fewMarkingsAtEnergy X e =
      ((X.bounded e).filter (fun b ↦ X.effective.energy b = e)).biUnion
        (fun b ↦ (dimensionShapes X e).image fun m ↦ (⟨2, b, m⟩ : SurfaceQuery X)) := by
  ext q
  rw [mem_fewMarkingsAtEnergy_iff]
  constructor
  · rintro ⟨⟨hg, _, _, hn, hd⟩, hE⟩
    refine Finset.mem_biUnion.mpr ⟨q.beta, Finset.mem_filter.mpr ⟨?_, hE⟩, ?_⟩
    · rw [X.bounded_eq, X.effective.mem_bounded, hE]
    · apply Finset.mem_image.mpr
      have hq : (⟨2, q.beta, q.insertions⟩ : SurfaceQuery X) = q :=
        (SurfaceQuery.eq_iff _ _).mpr ⟨hg.symm, rfl, rfl⟩
      refine ⟨q.insertions, ?_, hq⟩
      rw [← hE, mem_dimensionShapes_iff q.beta (by omega) _, hq]
      exact ⟨hn, hd⟩
  · intro h
    obtain ⟨b, hb, hm⟩ := Finset.mem_biUnion.mp h
    obtain ⟨m, hmem, rfl⟩ := Finset.mem_image.mp hm
    have hE := (Finset.mem_filter.mp hb).2
    have hpos : 0 < X.effective.energy b := by omega
    rw [← hE, mem_dimensionShapes_iff b hpos] at hmem
    refine ⟨⟨rfl, ?_, hE.trans_le h4, hmem.1, hmem.2⟩, hE⟩
    intro hzero
    change b = 0 at hzero
    rw [hzero, map_zero] at hpos
    omega
end AxiomaticGW.SurfaceGenusTwo
