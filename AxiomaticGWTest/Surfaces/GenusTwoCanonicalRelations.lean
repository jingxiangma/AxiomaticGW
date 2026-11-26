/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCanonicalRelations
public import AxiomaticGW.Surfaces.GenusTwoBlowupOrder
public import AxiomaticGW.Surfaces.GenusTwoBlowupPCoefficients

/-!
# Consumers of complete BP and L24 canonical-variable closure

The tests classify arbitrary actual variables rather than presupposing their
query shape. They retain full mixed exceptional coordinates, exclude a
dimension-compatible high-psi ancestor and the dimension-incompatible point
descendant at zero, and instantiate the classification at a proved nonzero
exceptional H column.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoCanonicalRelations
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo BelorousskiPandharipande

/-- The coefficient API supplies a family and exact effective-class remainder
for every actual surviving variable, including variables not given as queries. -/
theorem family_of_actual_dependency {X : SurfaceTarget} (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) (v : Variable X)
    (hc : RationalTerms.coefficient (normalizedGenusTwoTerms X n beta 0 a) {v} ≠ 0) :
    ∃ gamma : X.Curve, ∃ family : SurfaceGenusTwoBlowupOrder.Family X,
      v = Sum.inr (family.query gamma) ∧ ∃ delta : X.Curve, gamma + delta = beta := by
  obtain ⟨gamma, c, hq, hv, delta, hd⟩ :=
    normalized_primary_coefficient_canonical n beta a v hc
  obtain ⟨family, hf⟩ := SurfaceGenusTwoBlowupOrder.family_of_mem_canonicalQueries hq
  exact ⟨gamma, family, by rw [hf]; exact hv, delta, hd⟩

/-- This excluded ancestor is dimension compatible; its two psi powers, rather
than a dimension mismatch, distinguish it from the normalized terminal family. -/
theorem hirzebruchOne_highPsi_ancestor_absent :
    let q := SurfaceAncestorKey.ofLabels 2 (Fin 1) (by norm_num [StableArity])
      (0 : SurfaceTarget.hirzebruchOne.Curve) ![2] ![.unit]
    q.DimensionCompatible ∧ q.totalPsi = 2 ∧
      RationalTerms.coefficient
        (normalizedGenusTwoTerms .hirzebruchOne 3 ![2, 1] 0
          (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 3))
        {Sum.inl q} = 0 := by
  dsimp only
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  exact normalized_primary_ancestor_coefficient_eq_zero (X := .hirzebruchOne) 3 ![2, 1]
    (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 3)
    (SurfaceAncestorKey.ofLabels 2 (Fin 1) (by norm_num [StableArity])
      (0 : SurfaceTarget.hirzebruchOne.Curve) ![2] ![.unit])

/-- The collected mixed-class row retains a coordinatewise effective remainder;
the exceptional coordinates are not replaced by their shared plane degree. -/
theorem blowupTwo_collected_mixed_full_class_support (n : ℕ)
    {t : ℚ × Multiset (Variable .blowupTwo)}
    (ht : t ∈ RationalTerms.collect
      (normalizedGenusTwoTerms .blowupTwo n ![2, 3, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] n))) :
    t.2 = 0 ∨ ∃ gamma : SurfaceTarget.blowupTwo.Curve,
      ∃ c ∈ canonicalQueries .blowupTwo gamma,
        t.2 = {Sum.inr c} ∧ ∃ delta : SurfaceTarget.blowupTwo.Curve,
          gamma + delta = ![2, 3, 1] :=
  collected_normalized_primary_canonical_support (X := .blowupTwo) n ![2, 3, 1]
    (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] n) ht

/-- Natural subtraction does not introduce a class-zero point descendant into
any primary BP row, including rows of positive source class. -/
theorem class_zero_point_descendant_absent {X : SurfaceTarget} (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) :
    RationalTerms.coefficient (normalizedGenusTwoTerms X n beta 0 a)
      {Sum.inr (SurfaceFirstDescendant.query 2 0 .point 0)} = 0 := by
  by_contra hc
  obtain ⟨gamma, c, hq, hv, _⟩ := normalized_primary_coefficient_canonical
    n beta a (.inr (SurfaceFirstDescendant.query 2 0 .point 0)) hc
  have hdim := canonicalQueries_dimensionCompatible gamma hq
  have heq := Sum.inr.inj hv
  rw [← heq] at hdim
  have hdim' : (SurfaceFirstDescendant.query 2 (0 : X.Curve) .point
      (X.effective.energy 0 - 1)).DimensionCompatible := by
    simpa only [map_zero, Nat.zero_sub] using hdim
  exact ((point_first_dimensionCompatible_iff (0 : X.Curve)).mp hdim' rfl).elim

/-- Canonical classification has a nonvacuous exceptional-class consumer: the
existing exact H coefficient is eighteen even though its plane degree is zero. -/
theorem hirzebruchOne_exceptional_nonzero_canonical_dependency :
    ∃ gamma : SurfaceTarget.hirzebruchOne.Curve,
      ∃ c ∈ canonicalQueries .hirzebruchOne gamma,
        (Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0] .hyperplane 1) :
          Variable .hirzebruchOne) = Sum.inr c ∧
        ∃ delta : SurfaceTarget.hirzebruchOne.Curve, gamma + delta = ![1, 0] := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![1, 0] = 1 := by decide +kernel
  have hp := SurfaceGenusTwoBlowupPCoefficients.hyperplane_coefficient
    (X := .hirzebruchOne) ![1, 0] (by decide +kernel)
  simp only [he] at hp
  apply normalized_primary_coefficient_canonical (X := .hirzebruchOne)
    (SurfaceTarget.hirzebruchOne.effective.energy ![1, 0] - 1) ![1, 0]
    (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane]
      (SurfaceTarget.hirzebruchOne.effective.energy ![1, 0] - 1))
    (.inr (SurfaceFirstDescendant.query 2 ![1, 0] .hyperplane 1))
  rw [hp]
  norm_num

/-- The full primary L24 equation also classifies an arbitrary actual variable,
without assuming an H column or dropping its exceptional calibration tails. -/
theorem l24_family_of_actual_dependency {X : SurfaceTarget} (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) (v : Variable X)
    (hc : RationalTerms.coefficient
      (L24Relation.normalizedGenusTwoTerms X n beta 0 a) {v} ≠ 0) :
    ∃ gamma : X.Curve, ∃ family : SurfaceGenusTwoBlowupOrder.Family X,
      v = Sum.inr (family.query gamma) ∧ ∃ delta : X.Curve, gamma + delta = beta := by
  obtain ⟨gamma, c, hq, hv, delta, hd⟩ :=
    L24Relation.normalized_primary_coefficient_canonical n beta a v hc
  obtain ⟨family, hf⟩ := SurfaceGenusTwoBlowupOrder.family_of_mem_canonicalQueries hq
  exact ⟨gamma, family, by rw [hf]; exact hv, delta, hd⟩

/-- Dimension compatibility, rather than natural subtraction, again excludes
the zero-class point descendant from every complete primary L24 row. -/
theorem l24_class_zero_point_descendant_absent {X : SurfaceTarget} (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms.coefficient (L24Relation.normalizedGenusTwoTerms X n beta 0 a)
      {Sum.inr (SurfaceFirstDescendant.query 2 0 .point 0)} = 0 := by
  by_contra hc
  obtain ⟨gamma, c, hq, hv, _⟩ := L24Relation.normalized_primary_coefficient_canonical
    n beta a (.inr (SurfaceFirstDescendant.query 2 0 .point 0)) hc
  have hdim := canonicalQueries_dimensionCompatible gamma hq
  have heq := Sum.inr.inj hv
  rw [← heq] at hdim
  have hdim' : (SurfaceFirstDescendant.query 2 (0 : X.Curve) .point
      (X.effective.energy 0 - 1)).DimensionCompatible := by
    simpa only [map_zero, Nat.zero_sub] using hdim
  exact ((point_first_dimensionCompatible_iff (0 : X.Curve)).mp hdim' rfl).elim

end AxiomaticGWTest.SurfaceGenusTwoCanonicalRelations
