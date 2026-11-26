/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.Fixtures.GenusTwoShifted

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PointPullback
open AxiomaticGW GluingExpression

-- Arbitrary terminal values are computational data, without a GW axiom.
example (X : SurfaceTarget) (value : SurfaceVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] (z : CotangentTerm g S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    z.expression.pointContraction X (SurfacePointPullback.vertex X value)
      z.decoration z.labels beta n a =
      ((z.addMarkings n).map fun t ↦ (t.1 : ℚ) *
        t.2.expression.surfaceDecoratedEval X value t.2.decoration beta 0
          (SurfaceGenusZero.pointLabels a n)).sum :=
  SurfacePointPullback.contraction_eq X value z beta n a

-- Both the full variable and full source class remain arbitrary.
example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 3 → SurfaceBasisLabel X) (v : SurfacePolynomialReduction.Variable X) :
    BelorousskiPandharipande.pointCoefficient X n beta a v =
      RationalTerms.coefficient (BelorousskiPandharipande.normalizedGenusTwoTerms
        X n beta 0 (SurfaceGenusZero.pointLabels a n)) {v} :=
  BelorousskiPandharipande.pointCoefficient_eq_full X n beta a v

-- L24 keeps its full source combination and the same arbitrary class boundary.
example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) (v : SurfacePolynomialReduction.Variable X) :
    L24Relation.pointCoefficient X n beta a v =
      RationalTerms.coefficient (L24Relation.normalizedGenusTwoTerms
        X n beta 0 (SurfaceGenusZero.pointLabels a n)) {v} :=
  L24Relation.pointCoefficient_eq_full X n beta a v

private def oneValue (X : SurfaceTarget) : SurfaceVertexValues X ℚ :=
  fun _ _ _ _ _ _ _ ↦ 1

private def component (power : ℕ) : CotangentTerm 2 (Fin 1) :=
  .fundamental 2 _ (by norm_num [StableArity]) (fun _ ↦ power)

private def sample (X : SurfaceTarget) (power n : ℕ) : ℚ :=
  (component power).expression.pointContraction X
    (SurfacePointPullback.vertex X (oneValue X))
    (component power).decoration (component power).labels 0 n (fun _ ↦ .hyperplane)

-- These are formal contraction probes with all vertex values one, not GW values.
-- The one-psi pullback has 2^3-1 nonempty rational-tail placements.
example : sample .plane 1 3 = -20 := by decide +kernel

-- Repeated corrections at higher powers include positive signed terms.
example : sample .plane 2 3 = 34 := by decide +kernel

-- No cotangent factor means there is no negative correction.
example : sample .plane 0 3 = 1 := by decide +kernel

-- Signed exceptional inverse-metric contributions are not lost in compression.
example : sample .hirzebruchOne 1 2 = -5 := by decide +kernel

example : sample .blowupTwo 1 2 = -2 := by decide +kernel

-- A psi factor at a future loop branch is pulled back before contraction.
private def loopSource : CotangentTerm 1 (Option (Option (Fin 0))) :=
  .fundamental 1 _ (by norm_num [StableArity]) (fun s ↦ Option.elim s 1 (fun _ ↦ 0))

example : loopSource.nonseparating.expression.pointContraction .plane
    (SurfacePointPullback.vertex .plane (oneValue .plane))
    loopSource.nonseparating.decoration loopSource.nonseparating.labels 0 2
      (fun s ↦ Fin.elim0 s) = -24 := by decide +kernel

-- The whole graph has genus two, but has no genus-two vertex.
example : SurfaceGenusTwo.pointCoefficient .plane
    SurfaceGenusTwoShifted.planeLineHyperplane loopSource.nonseparating ![2] 2
      (fun s ↦ Fin.elim0 s) = 0 := by decide +kernel

-- The replay binds the claimed number to its actual complete equation.
example : RationalTerms.coefficient (BelorousskiPandharipande.normalizedGenusTwoTerms
    .plane 2 ![2] 0 (SurfaceGenusZero.pointLabels ![.point, .point, .point] 2))
      {SurfaceGenusTwoShifted.planeLineHyperplane} ≠ -17 := by
  rw [SurfaceGenusTwoShifted.planeLineHyperplane_full]
  norm_num

-- The shifted source really contains the primary column missing in earlier rows.
example : RationalTerms.coefficient (BelorousskiPandharipande.normalizedGenusTwoTerms
    .plane 3 ![2] 0 (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] 3))
      {SurfaceGenusTwoShifted.planeLinePrimary} ≠ 0 := by
  rw [SurfaceGenusTwoShifted.planeLinePrimary_full]
  norm_num

end AxiomaticGWTest.Surfaces.PointPullback
