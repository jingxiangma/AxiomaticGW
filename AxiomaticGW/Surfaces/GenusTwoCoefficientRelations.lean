/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCoefficientTerms
public import AxiomaticGW.Surfaces.GenusTwoPointCoefficients
public import AxiomaticGW.Surfaces.GenusTwoLeadingRelations

/-!
# Certified coefficient extraction across curve classes

The evaluator agrees with the complete normalized equations, without assuming
that the requested variable has the equation's curve class. Input-class
coefficients recover the previously verified leading evaluator.
-/

@[expose] public section

namespace AxiomaticGW
open RelationCertificate PsiBoundaryExpansion SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)

namespace BelorousskiPandharipande

/-- Every extracted entry belongs to the complete normalized BP equation. -/
theorem normalizedCoefficient_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    (v : Variable X) :
    normalizedCoefficient X n beta k a v =
      RationalTerms.coefficient (normalizedGenusTwoTerms X n beta k a) {v} := by
  simp only [normalizedGenusTwoTerms, genusTwoTerms, surfaceTerms,
    RationalTerms.coefficient_affineSubstitute_sum,
    RationalTerms.coefficient_affineSubstitute_scale,
    RationalTerms.coefficient_affineSubstitute_bind]
  change normalizedCoefficient X n beta k a v =
    ∑ i, rawPaperCoefficient i * ∑ e,
      (((orbitCotangentTerm i e).addMarkings n).map fun t ↦ (t.1 : ℚ) *
        SurfaceGenusTwo.normalizedCoefficient t.2.expression t.2.decoration beta k a v).sum
  have he (x : GluingExpression 2 (ExtraMarkings n (Fin 3))) (d : x.CotangentDecoration) :
      SurfaceGenusTwo.normalizedCoefficient x d beta k a v =
        SurfaceGenusTwo.coefficientEval X v x (by omega) d beta k a :=
    (SurfaceGenusTwo.coefficientEval_eq v x (by omega) d beta k a).symm
  simp only [he]
  rw [Fin.sum_univ_add (a := 4) (b := 16)]
  change normalizedCoefficient X n beta k a v = normalizedCoefficient X n beta k a v + _
  suffices hz : (∑ i : Fin 16, rawPaperCoefficient (Fin.natAdd 4 i) * ∑ e,
      (((orbitCotangentTerm (Fin.natAdd 4 i) e).addMarkings n).map fun t ↦ (t.1 : ℚ) *
        SurfaceGenusTwo.coefficientEval X v t.2.expression (by omega)
          t.2.decoration beta k a).sum) = 0 by rw [hz, add_zero]
  apply Finset.sum_eq_zero
  intro i _
  suffices hz : (∑ e : Fin 6,
      (((orbitCotangentTerm (Fin.natAdd 4 i) e).addMarkings n).map fun t ↦ (t.1 : ℚ) *
        SurfaceGenusTwo.coefficientEval X v t.2.expression (by omega)
          t.2.decoration beta k a).sum) = 0 by rw [hz, mul_zero]
  apply Finset.sum_eq_zero
  intro e _
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
  rw [SurfaceGenusTwo.coefficientEval_eq_zero_of_maxComponentGenus v t.2.expression (by omega)
    (added_term_lower_genus (Fin.natAdd 4 i) (by change 4 ≤ 4 + i.val; omega) e n t ht),
    mul_zero]

/-- The earlier leading evaluator remains the optimized input-class specialization. -/
theorem normalizedCoefficient_eq_leading (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    (v : Variable X) (hv : variableCurve v = beta) :
    normalizedCoefficient X n beta k a v = leadingCoefficient X n beta k a v := by
  rw [normalizedCoefficient_eq, leadingCoefficient_eq X n beta k a v hv]

/-- Binomial point compression preserves the complete normalized BP request. -/
theorem pointCoefficient_eq_full (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 3 → SurfaceBasisLabel X) (v : Variable X) :
    pointCoefficient X n beta a v =
      RationalTerms.coefficient
        (normalizedGenusTwoTerms X n beta 0 (SurfaceGenusZero.pointLabels a n)) {v} := by
  rw [pointCoefficient_eq, normalizedCoefficient_eq]

end BelorousskiPandharipande

namespace L24Relation

set_option maxRecDepth 20000

/-- Every extracted entry belongs to the complete normalized L24 equation. -/
theorem normalizedCoefficient_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (v : Variable X) :
    normalizedCoefficient X n beta k a v =
      RationalTerms.coefficient (normalizedGenusTwoTerms X n beta k a) {v} := by
  simp only [normalizedCoefficient, normalizedGenusTwoTerms, genusTwoTerms, surfaceTerms,
    RationalTerms.coefficient_affineSubstitute_bind,
    RationalTerms.coefficient_affineSubstitute_scale,
    SurfaceGenusTwo.coefficientEval_eq, SurfaceGenusTwo.normalizedCoefficient]

/-- Agreement with the existing input-class coefficient theorem. -/
theorem normalizedCoefficient_eq_leading (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (v : Variable X) (hv : variableCurve v = beta) :
    normalizedCoefficient X n beta k a v = leadingCoefficient X n beta k a v := by
  rw [normalizedCoefficient_eq, leadingCoefficient_eq X n beta k a v hv]

/-- Point compression preserves the coefficient of the complete L24 equation. -/
theorem pointCoefficient_eq_full (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) (v : Variable X) :
    pointCoefficient X n beta a v =
      RationalTerms.coefficient
        (normalizedGenusTwoTerms X n beta 0 (SurfaceGenusZero.pointLabels a n)) {v} := by
  rw [pointCoefficient_eq, normalizedCoefficient_eq]

end L24Relation
end AxiomaticGW
