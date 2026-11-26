/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.PointTarget.DVVCalculation
public import AxiomaticGW.Tautological.GluingForgetful
public import AxiomaticGW.CohFT.PsiGluing

/-! # Integrating cotangent classes on raw boundary strata

Each vertex contributes its point-target DVV expansion. Marking bijections transport powers,
and each node introduces two zero powers. The output retains unresolved vertex integrals.
Raw gluing maps carry no graph automorphism factor.
-/

@[expose] public section
namespace AxiomaticGW.PointTarget.DVVCalculation

variable {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C}

/-- The product of the point-target polynomials on the labeled components of a boundary stratum. -/
def graphExpansion (depth : ℕ) {g : ℕ} {S : Type} [Fintype S] :
    GluingExpression g S → (S → ℕ) → RationalTerms Key
  | @GluingExpression.fundamental g _ _ _, k => expand depth g (profile k)
  | @GluingExpression.relabel _ _ _ _ _ e x, k => graphExpansion depth x (k ∘ e)
  | @GluingExpression.separating _ _ _ _ _ _ x y, k =>
      RationalTerms.mul (graphExpansion depth x (PsiClasses.separatingLeftPowers k))
        (graphExpansion depth y (PsiClasses.separatingRightPowers k))
  | @GluingExpression.nonseparating _ _ _ x, k =>
      graphExpansion depth x (PsiClasses.nonseparatingPowers k)

/-- The symbolic vertex product integrates against the composite pushforward. -/
theorem graphExpansion_value (P : PsiClasses C) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (dvv : DVVRecursion P I)
    (zero : value P I 0 [0, 0, 0] = 1) (one : value P I 1 [1] = 1 / 24)
    (depth : ℕ) {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (k : S → ℕ) :
    RationalTerms.eval (fun t : Key ↦ value P I t.1 t.2) (graphExpansion depth x k) =
      I.integrate g S x.stable (P.monomial g S x.stable k * x.classValue F N) := by
  induction x with
  | fundamental g S h =>
    rw [graphExpansion, expand_value P I dvv zero one, value_profile,
      intersectionNumber_of_stable P I g S h, GluingExpression.classValue, mul_one]
  | @relabel g S T _ _ e x ih =>
    rw [graphExpansion, ih, GluingExpression.classValue,
      ← P.rename_monomial_comp g S T x.stable (x.relabel e).stable e k,
      ← map_mul (C.rename g S T x.stable (x.relabel e).stable e), I.integrate_rename]
  | @separating g h S T _ _ x y ihx ihy =>
    rw [graphExpansion, RationalTerms.eval_mul, ihx, ihy, GluingExpression.classValue,
      F.integrate_mul_push, P.separating_monomial, Algebra.TensorProduct.tmul_mul_tmul,
      I.tensorIntegral_tmul]
  | @nonseparating g S _ x ih =>
    rw [graphExpansion, ih, GluingExpression.classValue, N.integrate_mul_push,
      P.nonseparating_monomial]

/-- A collected constant for a list of raw strata certifies the integral of their sum.
This includes every placement of a forgotten marking with its multiplicity. -/
theorem graphList_constant (P : PsiClasses C) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (dvv : DVVRecursion P I)
    (zero : value P I 0 [0, 0, 0] = 1) (one : value P I 1 [1] = 1 / 24)
    (depth : ℕ) {g : ℕ} {S : Type} [Fintype S] (xs : List (GluingExpression g S))
    (h : StableArity g S) (k : S → ℕ) (a : ℚ)
    (ha : RationalTerms.collect ((xs.map fun x ↦ graphExpansion depth x k).sum) =
      RationalTerms.term a 0) :
    I.integrate g S h
      (P.monomial g S h k * (xs.map (GluingExpression.classValue F N)).sum) = a := by
  let L := (I.integrate g S h).comp (LinearMap.mulLeft ℚ (P.monomial g S h k))
  change L _ = a
  have he := congrArg (RationalTerms.eval (fun t : Key ↦ value P I t.1 t.2)) ha
  simp only [RationalTerms.eval_collect, RationalTerms.eval_list_sum, List.map_map,
    Function.comp_def, graphExpansion_value P F N dvv zero one, RationalTerms.eval_term,
    Multiset.map_zero, Multiset.prod_zero, Algebra.algebraMap_self_apply, mul_one] at he
  rw [map_list_sum, List.map_map]
  exact he

end AxiomaticGW.PointTarget.DVVCalculation
