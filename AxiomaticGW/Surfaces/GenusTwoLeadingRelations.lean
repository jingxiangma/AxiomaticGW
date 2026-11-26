/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoLeadingTerms
public import AxiomaticGW.Surfaces.GenusTwoNormalizedSupport

/-!
# Exact leading matrices for the complete BP and L24 families

The executable entries retain every original coefficient, signed cotangent
pullback and marking multiplicity. Only the computation of an input-class
coefficient is optimized; the equality theorems refer to the full normalized
equations. No rank or nonzero-pivot assertion is made here.
-/

@[expose] public section

namespace AxiomaticGW
open RelationCertificate PsiBoundaryExpansion SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)

namespace SurfaceGenusTwo
variable {X : SurfaceTarget}

/-- The executable result is the coefficient in the complete normalized
contraction, including its rational-tail corrections. -/
theorem leadingCoefficientEval_eq_normalized (beta : X.Curve) (v : Variable X)
    (hv : variableCurve v = beta) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g ≤ 2) (d : x.CotangentDecoration)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    leadingCoefficientEval X beta v x hg d k a =
      RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
        (x.surfaceDecoratedTerms X (vertexTerms X) d beta k a)) {v} := by
  rw [leadingCoefficientEval_eq beta v hv]
  exact (coefficient_normalized_eq_direct
    ((termsBound_decorated x d beta k a).mono hg) v hv).symm

end SurfaceGenusTwo

namespace BelorousskiPandharipande

/-- Every computed BP entry is the coefficient of the full normalized equation. -/
theorem leadingCoefficient_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    (v : Variable X) (hv : variableCurve v = beta) :
    leadingCoefficient X n beta k a v =
      RationalTerms.coefficient (normalizedGenusTwoTerms X n beta k a) {v} := by
  rw [normalizedGenusTwoTerms, SurfaceGenusTwo.coefficient_normalized_eq_direct
    (genusTwoTerms_bound X n beta k a) v hv]
  simp only [leadingCoefficient, genusTwoTerms, surfaceTerms,
    RationalTerms.coefficient_affineSubstitute_sum,
    RationalTerms.coefficient_affineSubstitute_scale,
    RationalTerms.coefficient_affineSubstitute_bind,
    SurfaceGenusTwo.leadingCoefficientEval_eq beta v hv, SurfaceGenusTwo.directCoefficient]

end BelorousskiPandharipande

namespace L24Relation

set_option maxRecDepth 20000

/-- Every computed L24 entry is the coefficient of the full normalized equation. -/
theorem leadingCoefficient_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (v : Variable X) (hv : variableCurve v = beta) :
    leadingCoefficient X n beta k a v =
      RationalTerms.coefficient (normalizedGenusTwoTerms X n beta k a) {v} := by
  rw [normalizedGenusTwoTerms, SurfaceGenusTwo.coefficient_normalized_eq_direct
    (genusTwoTerms_bound X n beta k a) v hv]
  simp only [leadingCoefficient, genusTwoTerms, surfaceTerms,
    RationalTerms.coefficient_affineSubstitute_bind,
    RationalTerms.coefficient_affineSubstitute_scale,
    SurfaceGenusTwo.leadingCoefficientEval_eq beta v hv, SurfaceGenusTwo.directCoefficient]

end L24Relation
end AxiomaticGW
