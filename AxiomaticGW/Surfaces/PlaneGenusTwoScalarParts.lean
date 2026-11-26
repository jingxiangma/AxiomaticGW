/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoScalar

/-!
# Component certificates for the complete plane genus-two scalars

Each component retains one original BP diagram and one of its six marking
assignments. Their exact sums recover the existing complete constants and
earlier coefficients. Checking these smaller expressions separately bounds
the size of an individual kernel reduction; it does not omit zero entries,
change normalization, or supply further invariant values.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfaceGenusTwo SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)

/-- One lower-genus diagram with its original marking assignment and raw weight. -/
def planePointConstantPart (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) (k : Fin 16) (e : Fin 6) : ℚ :=
  let z := orbitCotangentTerm (Fin.natAdd 4 k) e
  rawPaperCoefficient (Fin.natAdd 4 k) *
    SurfaceGenusOne.primaryGraphDimensionEval .plane
      planeRationalPointValue planeEllipticPointValue z.expression beta n a

/-- All sixteen diagrams and all six assignments retain their original multiplicities. -/
theorem planePointConstant_eq_sum_parts (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) :
    planePointConstant n beta a = ∑ k, ∑ e, planePointConstantPart n beta a k e := by
  simp only [planePointConstant, planePointConstantDiagram, planePointConstantPart,
    Finset.mul_sum]

/-- A shifted constant component, in the unchanged HHP/HPP/PPP row order. -/
def planeShiftedConstantPart (d : ℕ) (i : Fin 3) (k : Fin 16) (e : Fin 6) : ℚ :=
  match i.val with
  | 0 => planePointConstantPart (3 * d + 1) ![d + 1]
      ![.hyperplane, .hyperplane, .point] k e
  | 1 => planePointConstantPart (3 * d) ![d + 1] ![.hyperplane, .point, .point] k e
  | _ => planePointConstantPart (3 * d - 1) ![d + 1] ![.point, .point, .point] k e

/-- Component replay certifies exactly the original complete scalar constant. -/
theorem planeShiftedConstantFast_eq_sum_parts (d : ℕ) (i : Fin 3) :
    planeShiftedConstantFast d i = ∑ k, ∑ e, planeShiftedConstantPart d i k e := by
  fin_cases i <;> exact planePointConstant_eq_sum_parts _ _ _

/-- One retained genus-two diagram at the complete effective remainder. -/
def planePointCoefficientPart (n source : ℕ) (a : Fin 3 → SurfaceBasisLabel .plane)
    (v : Variable .plane) (k : Fin 4) (e : Fin 6) : ℚ :=
  if variableCurve v 0 ≤ source then
    let z := orbitCotangentTerm (Fin.castAdd 16 k) e
    rawPaperCoefficient (Fin.castAdd 16 k) *
      (if z.expression.maxComponentGenus = 2 then
        planeCachedRemainderContraction v (planeCachedRemainderVertex v) z.expression
          z.decoration z.labels ![source - variableCurve v 0] n a
       else 0)
  else 0

/-- The source-degree guard and every signed cotangent-tail contribution are preserved. -/
theorem planeCachedPointCoefficient_eq_sum_parts (n source : ℕ)
    (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) :
    planeCachedPointCoefficient n source a v =
      ∑ k, ∑ e, planePointCoefficientPart n source a v k e := by
  by_cases h : variableCurve v 0 ≤ source
  · simp only [planeCachedPointCoefficient, planeCachedRemainderPointCoefficient,
      planePointCoefficientPart, if_pos h, Finset.mul_sum]
  · simp only [planeCachedPointCoefficient, planePointCoefficientPart, if_neg h,
      Finset.sum_const_zero]

/-- One original component of an earlier canonical coefficient. -/
def planeEarlierCoefficientPart (d : ℕ) (i : Fin 3) (b : ℕ) (j : Fin 3)
    (k : Fin 4) (e : Fin 6) : ℚ :=
  let v : Variable .plane := Sum.inr (planeCanonicalQueries b j)
  match i.val with
  | 0 => planePointCoefficientPart (3 * d + 1) (d + 1)
      ![.hyperplane, .hyperplane, .point] v k e
  | 1 => planePointCoefficientPart (3 * d) (d + 1) ![.hyperplane, .point, .point] v k e
  | _ => planePointCoefficientPart (3 * d - 1) (d + 1) ![.point, .point, .point] v k e

/-- No coefficient is replaced by a sampled or guessed formula. -/
theorem planeEarlierCoefficient_eq_sum_parts (d : ℕ) (i : Fin 3) (b : ℕ) (j : Fin 3) :
    planeEarlierCoefficient d i b j = ∑ k, ∑ e, planeEarlierCoefficientPart d i b j k e := by
  fin_cases i <;> exact planeCachedPointCoefficient_eq_sum_parts _ _ _ _

end AxiomaticGW.BelorousskiPandharipande
