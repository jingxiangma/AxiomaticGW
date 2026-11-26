/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GluingCotangentDimension
public import AxiomaticGW.Surfaces.GenusOneAncestors

/-!
# Dimension vanishing for the reconstructed low-genus ancestors

The original genus-zero and genus-one algorithms vanish when total psi
degree exceeds `3*g - 3 + n`, at every effective class on each fixed surface.
This follows directly from their one-edge recursion and stable terminal
arities; it requires no geometric model or additional seed. The result also
holds at every fuel value, so no termination bound is needed for pruning.

The optional evaluation identities expose this zero branch before unfolding
lower-genus recursion. Their complementary branches are the unchanged
original evaluator, and no global simplification or evaluation rule is added.
-/

@[expose] public section

namespace AxiomaticGW.PsiBoundaryExpansion

/-- Every term in the original rational psi expansion has exactly one node. -/
theorem genusZeroTerms_edgeCount (s : Fin 3) (n : ℕ)
    (t : ℚ × GluingExpression 0 (ExtraMarkings n (Fin 3)))
    (ht : t ∈ genusZeroTerms s n) : t.2.graph.graph.edgeCount = 1 := by
  exact terms_edgeCount 0 (Fin 3) StableArity.zero_fin_three s []
    (fun _ h ↦ (List.not_mem_nil h).elim) n t ht

/-- The elliptic loop and all its pulled-back tails have exactly one node. -/
theorem genusOneTerms_edgeCount (n : ℕ)
    (t : ℚ × GluingExpression 1 (ExtraMarkings n (Fin 1)))
    (ht : t ∈ genusOneTerms n) : t.2.graph.graph.edgeCount = 1 := by
  apply terms_edgeCount 1 (Fin 1) GenusOnePsi.stableArity 0
    [(1 / 24, GenusOnePsi.loopExpression)] _ n t ht
  intro z hz
  simp only [List.mem_singleton] at hz
  subst z
  rfl
end AxiomaticGW.PsiBoundaryExpansion

namespace AxiomaticGW.SurfaceGenusZero
variable {X : SurfaceTarget}

/-- The selected marking removes exactly one cotangent power. -/
theorem sum_lowerAncestorPowers_add_one (q : SurfaceAncestorKey X)
    (hg : q.genus = 0) (hp : ¬q.IsPrimary) :
    (∑ s, lowerAncestorPowers q hg hp s) + 1 = q.totalPsi := by
  letI := ExtraMarkings.decidableEq (Fin 3) (extraCount q)
  have hs := congrArg (fun k : ExtraMarkings (extraCount q) (Fin 3) → ℕ ↦ ∑ s, k s)
    (lowerAncestorPowers_restore q hg hp)
  simpa only [Pi.add_apply, Finset.sum_add_distrib, Pi.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Function.comp_apply,
    Equiv.sum_comp, q.sum_orderedPowers] using hs

/-- Every fuel approximation vanishes above the stable-curve cotangent dimension. -/
theorem ancestorValueFuel_zero_of_cotangent_bound (fuel : ℕ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 0) (hd : q.insertions.card ≤ q.totalPsi + 2) :
    ancestorValueFuel X fuel q = 0 := by
  induction fuel generalizing q with
  | zero =>
      have hp : ¬q.IsPrimary := by
        intro hp
        have hz := q.totalPsi_eq_zero_iff.mpr hp
        have hs := q.stable
        rw [hg] at hs
        omega
      rw [ancestorValueFuel, if_neg (fun h ↦ hp h.2)]
  | succ fuel ih =>
      have hp : ¬q.IsPrimary := by
        intro hp
        have hz := q.totalPsi_eq_zero_iff.mpr hp
        have hs := q.stable
        rw [hg] at hs
        omega
      rw [ancestorValueFuel, dif_pos hg, dif_neg hp, ancestorStep]
      apply List.sum_eq_zero
      intro c hc
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
      rw [t.2.surfaceEval_zero_of_cotangent_bound X _ q.beta _ _]
      · exact mul_zero _
      · intro g' S' _ h' beta' k' a' hgen hdegree
        have hz : g' = 0 := Nat.eq_zero_of_le_zero hgen
        subst g'
        apply ih _ rfl
        rw [SurfaceAncestorKey.totalPsi_ofLabels]
        simpa only [SurfaceAncestorKey.ofLabels, Multiset.card_map, Finset.card_val,
          Finset.card_univ, Nat.mul_zero, Nat.zero_add] using hdegree
      · have hs := sum_lowerAncestorPowers_add_one q hg hp
        have he := PsiBoundaryExpansion.genusZeroTerms_edgeCount 0 (extraCount q) t ht
        have hc : Fintype.card (ExtraMarkings (extraCount q) (Fin 3)) = q.insertions.card :=
          (Fintype.card_congr (ancestorFrame q hg hp)).trans (by
            rw [Fintype.card_fin, q.orderedInsertions_length])
        rw [Nat.mul_zero, Nat.zero_add, he, hc]
        omega

/-- The original terminating algorithm respects stable-curve dimension vanishing. -/
theorem ancestorValue_zero_of_cotangent_bound (q : SurfaceAncestorKey X)
    (hg : q.genus = 0) (hd : q.insertions.card ≤ q.totalPsi + 2) :
    ancestorValue X q = 0 := ancestorValueFuel_zero_of_cotangent_bound _ q hg hd

/-- An optional computation rule with the unchanged algorithm outside the zero branch. -/
theorem ancestorValue_pruned (q : SurfaceAncestorKey X) :
    ancestorValue X q =
      if q.genus = 0 ∧ q.insertions.card ≤ q.totalPsi + 2 then 0
      else ancestorValueFuel X q.totalPsi q := by
  split_ifs with h
  · exact ancestorValue_zero_of_cotangent_bound q h.1 h.2
  · rfl

end AxiomaticGW.SurfaceGenusZero

namespace AxiomaticGW.SurfaceGenusOne
variable {X : SurfaceTarget}

/-- The selected marking removes exactly one cotangent power. -/
theorem sum_lowerAncestorPowers_add_one (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hp : ¬q.IsPrimary) :
    (∑ s, lowerAncestorPowers q hg hp s) + 1 = q.totalPsi := by
  letI := ExtraMarkings.decidableEq (Fin 1) (extraCount q)
  have hs := congrArg (fun k : ExtraMarkings (extraCount q) (Fin 1) → ℕ ↦ ∑ s, k s)
    (lowerAncestorPowers_restore q hg hp)
  simpa only [Pi.add_apply, Finset.sum_add_distrib, Pi.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Function.comp_apply,
    Equiv.sum_comp, q.sum_orderedPowers] using hs

/-- Every fuel approximation vanishes above the stable-curve cotangent dimension. -/
theorem ancestorValueFuel_zero_of_cotangent_bound (fuel : ℕ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hd : q.insertions.card < q.totalPsi) :
    ancestorValueFuel X fuel q = 0 := by
  induction fuel generalizing q with
  | zero =>
      have hp : ¬q.IsPrimary := by
        intro hp
        have hz := q.totalPsi_eq_zero_iff.mpr hp
        omega
      rw [ancestorValueFuel, if_neg (fun h ↦ hp h.2)]
  | succ fuel ih =>
      have hp : ¬q.IsPrimary := by
        intro hp
        have hz := q.totalPsi_eq_zero_iff.mpr hp
        omega
      rw [ancestorValueFuel, dif_pos hg, dif_neg hp, ancestorStep]
      apply List.sum_eq_zero
      intro c hc
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
      rw [t.2.surfaceEval_zero_of_cotangent_bound X _ q.beta _ _]
      · exact mul_zero _
      · intro g' S' _ h' beta' k' a' hgen hdegree
        by_cases hz : g' = 0
        · subst g'
          change SurfaceGenusZero.ancestorValue X
            (SurfaceAncestorKey.ofLabels 0 S' h' beta' k' a') = 0
          apply SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound _ rfl
          rw [SurfaceAncestorKey.totalPsi_ofLabels]
          simpa only [SurfaceAncestorKey.ofLabels, Multiset.card_map, Finset.card_val,
            Finset.card_univ, Nat.mul_zero, Nat.zero_add] using hdegree
        · have ho : g' = 1 := by omega
          subst g'
          change ancestorValueFuel X fuel
            (SurfaceAncestorKey.ofLabels 1 S' h' beta' k' a') = 0
          apply ih _ rfl
          rw [SurfaceAncestorKey.totalPsi_ofLabels]
          simp only [SurfaceAncestorKey.ofLabels, Multiset.card_map, Finset.card_val,
            Finset.card_univ]
          omega
      · have hs := sum_lowerAncestorPowers_add_one q hg hp
        have he := PsiBoundaryExpansion.genusOneTerms_edgeCount (extraCount q) t ht
        have hc : Fintype.card (ExtraMarkings (extraCount q) (Fin 1)) = q.insertions.card :=
          (Fintype.card_congr (ancestorFrame q hg hp)).trans (by
            rw [Fintype.card_fin, q.orderedInsertions_length])
        rw [Nat.mul_one, he, hc]
        omega

/-- The original terminating algorithm respects stable-curve dimension vanishing. -/
theorem ancestorValue_zero_of_cotangent_bound (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hd : q.insertions.card < q.totalPsi) :
    ancestorValue X q = 0 := ancestorValueFuel_zero_of_cotangent_bound _ q hg hd

/-- An optional computation rule with the unchanged algorithm outside the zero branch. -/
theorem ancestorValue_pruned (q : SurfaceAncestorKey X) :
    ancestorValue X q =
      if q.genus = 1 ∧ q.insertions.card < q.totalPsi then 0
      else ancestorValueFuel X q.totalPsi q := by
  split_ifs with h
  · exact ancestorValue_zero_of_cotangent_bound q h.1 h.2
  · rfl

end AxiomaticGW.SurfaceGenusOne
