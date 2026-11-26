/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneShiftedSystem
public import AxiomaticGW.Coefficients.TermSupport

/-!
# Canonical support of low-power plane normalization

Every genus-two primary or first-power plane ancestor normalizes to the three
canonical requests at its exact curve degree. The integer dimension equation
fixes each point count, including at degree zero. Higher powers are excluded
by an explicit hypothesis; their absence from a particular equation must be
proved separately.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceFirstDescendant
open BelorousskiPandharipande

private theorem mem_dimensionTerms {q : SurfaceQuery .plane}
    {t : ℚ × Multiset (SurfaceQuery .plane)} (ht : t ∈ dimensionTerms q) :
    t.2 = {q} ∧ q.DimensionCompatible := by
  unfold dimensionTerms at ht
  split_ifs at ht with hd
  · exact ⟨congrArg Prod.snd (RationalTerms.mem_term.mp ht).2, hd⟩
  · exact (Multiset.notMem_zero _ ht).elim

/-- A surviving primary query has exactly the genus-two primary point count. -/
theorem primaryTerms_plane_canonical_support (d : ℕ)
    (m : Multiset (SurfaceBasisLabel .plane)) {t : ℚ × Multiset (SurfaceQuery .plane)}
    (ht : t ∈ primaryTerms 2 ![d] m) : t.2 = {planeCanonicalQueries d 0} := by
  obtain ⟨_, s, hs, rfl⟩ := RationalTerms.mem_scale.mp ht
  obtain ⟨hm, hd⟩ := mem_dimensionTerms hs
  rw [SurfaceQuery.dimensionCompatible_points_plane] at hd
  have hn : m.count .point = 3 * d + 1 := by omega
  rw [hm, hn]
  rfl

private theorem primary_dimension_canonical (d n : ℕ)
    {t : ℚ × Multiset (SurfaceQuery .plane)}
    (ht : t ∈ dimensionTerms (SurfaceQuery.points .plane 2 ![d] n)) :
    t.2 = {planeCanonicalQueries d 0} := by
  obtain ⟨hm, hd⟩ := mem_dimensionTerms ht
  rw [SurfaceQuery.dimensionCompatible_points_plane] at hd
  have hn : n = 3 * d + 1 := by omega
  rw [hm, hn]
  rfl

/-- Unit, divisor and cup-product corrections introduce no fourth family. -/
theorem terms_plane_canonical_support (d : ℕ) (b : SurfaceBasisLabel .plane)
    (m : Multiset (SurfaceBasisLabel .plane)) {t : ℚ × Multiset (SurfaceQuery .plane)}
    (ht : t ∈ terms 2 ![d] b m) : ∃ j, t.2 = {planeCanonicalQueries d j} := by
  unfold terms at ht
  split_ifs at ht with hu hb
  · exact ⟨0, primaryTerms_plane_canonical_support d _ ht⟩
  · obtain ⟨_, s, hs, rfl⟩ := RationalTerms.mem_scale.mp ht
    exact ⟨0, primaryTerms_plane_canonical_support d _ (t := s) hs⟩
  · rcases Multiset.mem_add.mp ht with ht | ht
    · obtain ⟨_, s, hs, rfl⟩ := RationalTerms.mem_scale.mp ht
      obtain ⟨hm, hd⟩ := mem_dimensionTerms hs
      rw [SurfaceQuery.dimensionCompatible_first_plane] at hd
      cases b with
      | unit => exact (hb rfl).elim
      | hyperplane =>
        have hn : m.count .point = 3 * d := by
          simp only [SurfaceBasisLabel.codimension] at hd
          omega
        refine ⟨1, ?_⟩
        rw [hm, hn]
        rfl
      | point =>
        have hn : m.count .point = 3 * d - 1 := by
          simp only [SurfaceBasisLabel.codimension] at hd
          omega
        refine ⟨2, ?_⟩
        rw [hm, hn]
        rfl
      | exceptional i => exact Fin.elim0 i
    · obtain ⟨_, s, hs, rfl⟩ := RationalTerms.mem_scale.mp ht
      exact ⟨0, primary_dimension_canonical d _ (t := s) hs⟩

end AxiomaticGW.SurfaceFirstDescendant

namespace AxiomaticGW.SurfacePolynomialReduction
open BelorousskiPandharipande

/-- A low-power genus-two plane component produces only a canonical descendant
variable at its full original curve class; no ancestor tag remains. -/
theorem normalizedTerms_plane_canonical_support (q : SurfaceAncestorKey .plane)
    (hg : q.genus = 2) (hk : q.totalPsi ≤ 1)
    {t : ℚ × Multiset (Variable .plane)} (ht : t ∈ normalizedTerms q) :
    ∃ j, t.2 = {Sum.inr (planeCanonicalQueries (q.beta 0) j)} := by
  have hb : q.beta = ![q.beta 0] := by
    funext i
    fin_cases i
    rfl
  rw [normalizedTerms_plane_eq_direct, directNormalizedTerms] at ht
  split_ifs at ht with h
  · obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
    rw [hg, hb] at hs
    obtain ⟨j, hj⟩ := SurfaceFirstDescendant.terms_plane_canonical_support _ _ _ hs
    exact ⟨j, by rw [hj, Multiset.map_singleton]⟩
  · have hz : q.totalPsi = 0 := by
      have hne : q.totalPsi ≠ 1 := fun he ↦ h ⟨by omega, he⟩
      omega
    have hp := q.totalPsi_eq_zero_iff.mp hz
    rw [canonicalPrimaryTerms, if_pos ⟨by omega, hp⟩] at ht
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
    rw [hg, hb] at hs
    exact ⟨0, by rw [SurfaceFirstDescendant.primaryTerms_plane_canonical_support _ _ hs,
      Multiset.map_singleton]⟩

end AxiomaticGW.SurfacePolynomialReduction
