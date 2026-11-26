/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusTwoLeadingRelations

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoLeading
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo
open SurfaceGenusZero (variableCurve)
open RelationCertificate PsiBoundaryExpansion

-- Full-family interfaces cover arbitrary powers, classes and added markings.
example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    (v : Variable X) (hv : variableCurve v = beta) :
    BelorousskiPandharipande.leadingCoefficient X n beta k a v =
      RationalTerms.coefficient (BelorousskiPandharipande.normalizedGenusTwoTerms
        X n beta k a) {v} := BelorousskiPandharipande.leadingCoefficient_eq X n beta k a v hv

example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (v : Variable X) (hv : variableCurve v = beta) :
    L24Relation.leadingCoefficient X n beta k a v =
      RationalTerms.coefficient (L24Relation.normalizedGenusTwoTerms X n beta k a) {v} :=
  L24Relation.leadingCoefficient_eq X n beta k a v hv

private abbrev genusTwoVertex : GluingExpression 2 (Option (Fin 0)) :=
  .fundamental 2 _ (by norm_num [StableArity])

private abbrev rationalVertex : GluingExpression 0 (Option (Fin 2)) :=
  .fundamental 0 _ (by norm_num [StableArity])

private abbrev tail : GluingExpression 2 (Fin 0 ⊕ Fin 2) :=
  genusTwoVertex.separating rationalVertex

private def pairLabels {X : SurfaceTarget} (a b : SurfaceBasisLabel X) :
    Fin 0 ⊕ Fin 2 → SurfaceBasisLabel X := Sum.elim Fin.elim0 ![a, b]

private def zeroPoint (X : SurfaceTarget) : Variable X :=
  .inr (SurfaceQuery.points X 2 0 1)

-- The zero split is counted once: the genus-two unknown has coefficient one.
example : leadingCoefficientEval .plane 0 (zeroPoint .plane) tail (by decide +kernel)
    (0, 0) 0 (pairLabels .hyperplane .hyperplane) = 1 := by decide +kernel

-- The generic theorem certifies this in the full normalized contraction.
example : RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (tail.surfaceDecoratedTerms .plane (vertexTerms .plane) (0, 0) 0 0
        (pairLabels .hyperplane .hyperplane))) {zeroPoint .plane} = 1 := by
  rw [← leadingCoefficientEval_eq_normalized 0 (zeroPoint .plane) rfl tail (by omega)]
  decide +kernel

-- The exceptional square has its required negative sign in the class-zero factor.
example : leadingCoefficientEval .hirzebruchOne 0 (zeroPoint .hirzebruchOne)
    tail (by decide +kernel) (0, 0) 0 (pairLabels (.exceptional 0) (.exceptional 0)) = -1 := by
  decide +kernel

private def exceptionalPsi : Variable .hirzebruchOne :=
  .inr ⟨2, 0, [⟨.exceptional 0, 1⟩]⟩

-- The inverse exceptional metric also contributes a minus sign. Node psi is retained.
example : leadingCoefficientEval .hirzebruchOne 0 exceptionalPsi tail (by decide +kernel)
    (fun _ ↦ 1, 0) 0 (pairLabels .unit (.exceptional 0)) = 1 := by decide +kernel

private def positivePointPsi : Variable .hirzebruchOne :=
  .inr ⟨2, ![1,0], [⟨.point, 1⟩]⟩

-- Positive input class stays on the genus-two vertex.
example : leadingCoefficientEval .hirzebruchOne ![1,0] positivePointPsi tail (by decide +kernel)
    (fun _ ↦ 1, 0) 0 (pairLabels .hyperplane .hyperplane) = 1 := by decide +kernel

-- Swapping the components gives the other term in the proved product rule.
example : leadingCoefficientEval .hirzebruchOne ![1,0] positivePointPsi
    (rationalVertex.separating genusTwoVertex) (by decide +kernel) (0, fun _ ↦ 1) 0
    (Sum.elim (fun _ ↦ .hyperplane) Fin.elim0) = 1 := by decide +kernel

private abbrev loop : GluingExpression 2 (Fin 1) :=
  (GluingExpression.fundamental 1 (Option (Option (Fin 1)))
    (by norm_num [StableArity])).nonseparating

-- Genus contributed by a loop leaves no genus-two component variable.
example : leadingCoefficientEval .plane 0 (zeroPoint .plane) loop (by decide +kernel)
    (fun _ ↦ 4) (fun _ ↦ 3) (fun _ ↦ .point) = 0 := by decide +kernel

private def highPsi : SurfaceAncestorKey .plane :=
  SurfaceAncestorKey.ofLabels 2 (Option (Fin 0)) genusTwoVertex.stable ![1]
    (fun _ ↦ 3) (fun _ ↦ .point)

-- Higher powers preserve their ancestor interpretation rather than a descendant tag.
example : leadingCoefficientEval .plane ![1] (.inl highPsi) genusTwoVertex (by decide +kernel)
    (fun _ ↦ 2) (fun _ ↦ 1) (fun _ ↦ .point) = 1 := by decide +kernel

-- Equal energy never merges the two exceptional curve classes.
example : leadingCoefficientEval .blowupTwo ![1,0,0]
    (.inr ⟨2, ![0,1,0], [⟨.point, 1⟩]⟩) tail (by decide +kernel)
      (fun _ ↦ 1, 0) 0 (pairLabels .hyperplane .hyperplane) = 0 := by decide +kernel

-- The generic product rule needs its constant-factor hypothesis: x² is nonlinear.
example : RationalTerms.coefficient
    (RationalTerms.affineSubstitute (fun _ : Fin 1 ↦ RationalTerms.term 1 {(0 : Fin 1)})
      (RationalTerms.mul (RationalTerms.term 1 {(0 : Fin 1)})
        (RationalTerms.term 1 {(0 : Fin 1)}))) {0} = 2 := by decide +kernel

end AxiomaticGWTest.Surfaces.GenusTwoLeading
