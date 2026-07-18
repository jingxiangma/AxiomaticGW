/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BasicStrata
public import AxiomaticGW.PointTarget.Descendants
public import Mathlib.Tactic.NormNum

/-!
# Low-genus tautological checks

In genus zero the top psi-class intersections are multinomial coefficients:

`integral_(Mbar_(0,n)) prod_i psi_i^(k_i) = (n-3)! / prod_i k_i!`

when the exponents sum to `n - 3`, and they vanish otherwise. The rational
function below makes this formula executable. `GenusZeroPsiFormula` remains a
separate geometric certificate connecting the numerical formula to a chosen
`StableCurveCohomology` realization.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

namespace PointTarget

/-- Exponents with a single nonzero descendant insertion. -/
def singlePsiExponent {n : ℕ} (i : Fin n) (d : ℕ) : Fin n → ℕ :=
  fun j ↦ if j = i then d else 0

/-- Exponents `(1, 1, 0, 0, 0)` used for the first nontrivial
genus-zero multinomial check. -/
def zeroFiveTwoPsiExponent : Fin 5 → ℕ :=
  Fin.cases 1 (Fin.cases 1 (fun _ : Fin 3 ↦ 0))

/-- The standard genus-zero psi-class intersection value. The stability test
prevents the subtraction `n - 3` from assigning a spurious value to an
unstable arity. -/
def genusZeroPsiValue (n : ℕ) (k : Fin n → ℕ) : ℚ :=
  if 3 ≤ n ∧ (∑ i, k i) = n - 3 then
    (Nat.factorial (n - 3) : ℚ) / ∏ i, Nat.factorial (k i)
  else 0

theorem genusZeroPsiValue_eq_zero_of_degree_ne (n : ℕ) (k : Fin n → ℕ)
    (hdegree : (∑ i, k i) ≠ n - 3) : genusZeroPsiValue n k = 0 := by
  simp only [genusZeroPsiValue, hdegree, and_false, ↓reduceIte]

theorem genusZeroPsiValue_zero_three :
    genusZeroPsiValue 3 (fun _ ↦ 0) = 1 := by
  norm_num [genusZeroPsiValue, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem genusZeroPsiValue_zero_four :
    genusZeroPsiValue 4 (singlePsiExponent 0 1) = 1 := by
  norm_num [genusZeroPsiValue, singlePsiExponent, Fin.sum_univ_succ,
    Fin.prod_univ_succ]

theorem genusZeroPsiValue_zero_five_two_psi :
    genusZeroPsiValue 5 zeroFiveTwoPsiExponent = 2 := by
  norm_num [genusZeroPsiValue, zeroFiveTwoPsiExponent,
    Fin.sum_univ_succ, Fin.prod_univ_succ]

/-- Four marked points in genus zero form a stable arity. -/
theorem genusZero_four_stable : StableArity 0 (Fin 4) := by
  norm_num [StableArity]

/-- A geometric realization satisfies the genus-zero psi formula when its
abstract intersection map agrees with the standard multinomial values. This
is additional geometric input, not a consequence of degree bookkeeping. -/
structure GenusZeroPsiFormula {R : Type*} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (P : PsiClasses C)
    (I : StableCurveIntegration C) : Prop where
  formula : ∀ (n : ℕ) (_h : StableArity 0 (Fin n)) (k : Fin n → ℕ),
    intersectionNumber P I 0 (Fin n) k =
      algebraMap ℚ R (genusZeroPsiValue n k)

theorem intersectionNumber_zero_four_of_formula
    {R : Type*} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (P : PsiClasses C)
    (I : StableCurveIntegration C) (F : GenusZeroPsiFormula P I) :
    intersectionNumber P I 0 (Fin 4) (singlePsiExponent 0 1) = 1 := by
  rw [F.formula 4 genusZero_four_stable]
  simp only [genusZeroPsiValue_zero_four, map_one]

end PointTarget

end AxiomaticGW
