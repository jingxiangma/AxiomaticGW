module

import AxiomaticGW.Surfaces.ExceptionalEvaluationSupport

-- This module consists of anonymous consumer regressions.
set_option linter.privateModule false

open AxiomaticGW SurfaceGenusTwo

-- Positive exceptional multiples with a point are accepted at arbitrary powers.
example : exceptionalPointQueryValue?
    (⟨2, ![3,0], [⟨.point, 3⟩]⟩ : SurfaceQuery .hirzebruchOne) = some 0 := by
  decide +kernel

-- Both disjoint exceptional coordinates are retained, including mixed classes.
example : exceptionalPointQueryValue?
    (⟨2, ![2,3,0], [⟨.point, 5⟩]⟩ : SurfaceQuery .blowupTwo) = some 0 := by
  decide +kernel

-- Equal anticanonical energy does not identify the curve classes.
example : exceptionalPointQueryValue?
    (⟨2, ![1,1], [⟨.point, 3⟩]⟩ : SurfaceQuery .hirzebruchOne) = none := by
  decide +kernel

example : exceptionalPointQueryValue?
    (⟨2, ![2,2,1], [⟨.point, 5⟩]⟩ : SurfaceQuery .blowupTwo) = none := by
  decide +kernel

-- Degree-zero primary values remain a separate initial-value deduction.
example : exceptionalPointQueryValue?
    (SurfaceQuery.points .hirzebruchOne 2 0 1) = none := by
  decide +kernel

-- Descendants supported on the exceptional curve need not vanish without a point.
example : exceptionalPointQueryValue?
    (⟨2, ![1,0], [⟨.unit, 3⟩]⟩ : SurfaceQuery .hirzebruchOne) = none := by
  decide +kernel

example : exceptionalPointQueryValue?
    (⟨2, ![1], [⟨.point, 3⟩]⟩ : SurfaceQuery .plane) = none := by
  decide +kernel

-- Positive degree is geometric even when the stabilized curve arity is unstable.
example : exceptionalPointQueryValue?
    (⟨0, ![2, 0], [⟨.point, 0⟩]⟩ : SurfaceQuery .hirzebruchOne) = some 0 := by
  decide +kernel

example :
    (⟨0, ![2, 0], [⟨.point, 0⟩]⟩ : SurfaceQuery .hirzebruchOne).GeometricDomain ∧
      ¬StableArity 0 (Fin 1) ∧
      (⟨0, ![2, 0], [⟨.point, 0⟩]⟩ : SurfaceQuery .hirzebruchOne).DimensionCompatible := by
  unfold StableArity
  decide +kernel

section Interpretation
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  {U : UnstableDescendantConventions M I}
  (G : StableMapIntersection U) (hG : ExceptionalPointSupport G)

-- The entire partial evaluator composes with the original geometric-domain query API.
example (q : SurfaceQuery X) (v : ℚ) (h : exceptionalPointQueryValue? q = some v) :
    q.checkedEval U = some v := exceptionalPointQueryValue?_sound G hG q v h

example (beta : X.Curve) (hb : beta ≠ 0) (hd : X.divisorIntersections beta 0 = 0)
    (q : SurfaceQuery X) (hq : q ∈ canonicalQueries X beta) : q.checkedEval U = some 0 :=
  exceptional_canonical_checkedEval_eq_zero G hG beta hb hd q hq

-- No genus-two value family is supplied to prove any of the four canonical sectors.
example (beta : X.Curve) (hb : beta ≠ 0) (hd : X.divisorIntersections beta 0 = 0) :
    (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1)).eval U = 0 :=
  exceptional_primary_eval_eq_zero G hG beta hb hd

example (beta : X.Curve) (hb : beta ≠ 0) (hd : X.divisorIntersections beta 0 = 0) :
    (SurfaceFirstDescendant.query 2 beta .hyperplane (X.effective.energy beta)).eval U = 0 :=
  exceptional_first_divisor_eval_eq_zero G hG beta hb hd .hyperplane

example (beta : X.Curve) (hb : beta ≠ 0) (hd : X.divisorIntersections beta 0 = 0)
    (i : Fin X.blowups) :
    (SurfaceFirstDescendant.query 2 beta (.exceptional i)
      (X.effective.energy beta)).eval U = 0 :=
  exceptional_first_divisor_eval_eq_zero G hG beta hb hd (.exceptional i)

example (beta : X.Curve) (hb : beta ≠ 0) (hd : X.divisorIntersections beta 0 = 0) :
    (SurfaceFirstDescendant.query 2 beta .point (X.effective.energy beta - 1)).eval U = 0 :=
  exceptional_first_point_eval_eq_zero G hG beta hb hd
end Interpretation
