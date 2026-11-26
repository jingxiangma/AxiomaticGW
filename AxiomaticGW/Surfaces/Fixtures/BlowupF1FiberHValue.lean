/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.Replay

/-!
# The first F1 fiber hyperplane descendant

The full query is genus two, target F=(0,1), one tau_1(H) insertion and two
primary point insertions. Its formal reconstructed value is zero. Equality
with a geometric GW evaluation uses the existing original-equation soundness
API, including exceptional point support and the finite genus-two divisor
seeds. No such geometric inputs are constructed or newly postulated here.
This is one canonical descendant, not a completed benchmark family.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberHValue
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open BlowupF1FiberHReduction BlowupF1FiberHZeroValues

/-- The requested full descendant key, including both primary point insertions. -/
def query : SurfaceQuery target := SurfaceFirstDescendant.query 2 ![0, 1] .hyperplane 2

/-- The numerical theorem refers to precisely this full canonical query. -/
theorem query_eq : query = Family.hyperplane.query fiber := by decide +kernel

/-- The actual descendant has the expected virtual dimension. -/
theorem query_dimensionCompatible : query.DimensionCompatible := by decide +kernel

/-- Existing query recognition recovers the same complete reconstruction state. -/
theorem state_query : state? query = some fiberState := by
  rw [query_eq, state?_query]

/-- The public canonical valuation supplies the proved formal value at the exact full query. -/
theorem reconstructed_query :
    canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0) (.inr query) = 0 := by
  rw [query_eq, canonicalValuation_query]
  exact reconstructed_fiber_h

/-- The existing original-equation soundness theorem transfers this one value to GW evaluation.
The BP/L24 hypotheses are the unchanged unsolved equations, not a numerical recurrence. -/
theorem eval_eq_zero_of_original_equations
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology target.blowups)
      target.Curve target.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification target Omega)
    (V : StableMapIntersection U) (hV : ExceptionalPointSupport V)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed target).query.eval U = -1 / 960)
    (hEtwo : ∀ j, (SurfaceSeed.genusTwoExceptional j : SurfaceSeed target).query.eval U =
      -1 / 2880)
    (hBP : ∀ n beta a, RationalTerms.eval (variableEval U P)
      (SurfaceGenusTwoBlowupNRelation.bpRow target n beta a) = 0)
    (hL : ∀ n beta (a : Fin 4 → SurfaceBasisLabel target),
      RationalTerms.eval (variableEval U P)
        (L24Relation.normalizedGenusTwoTerms target n beta 0
          (SurfaceGenusZero.pointLabels a n)) = 0) : query.eval U = 0 := by
  rw [query_eq]
  have h := SurfaceGenusTwoBlowupRecursion.values_eq_eval_of_original_equations
    0 U P T V hV hHtwo hEtwo hBP hL fiberState
  exact h.symm.trans reconstructed_fiber_h

end AxiomaticGW.BlowupF1FiberHValue
