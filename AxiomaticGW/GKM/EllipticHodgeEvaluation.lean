/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.EllipticHodge
public import AxiomaticGW.PointTarget.DVVTermination

/-! # Complete genus-one Hodge integrals for a surface localization vertex

Each tangent direction contributes either the unit or the first Chern class. The
zero Hodge-index pair uses the point-target recursion, one positive index uses
the elliptic multinomial, and the pair with two positive indices vanishes.
-/

@[expose] public section
namespace AxiomaticGW.GKM.EllipticHodge
open PointTarget.DVVCalculation PsiBoundaryExpansion

/-- The three numerical branches used by the genus-one surface vertex. Both marking labels
and repeated powers are retained. -/
def nativeMoment {S : Type} [Fintype S] (i j : Fin 2) (d : S → ℕ) : ℚ :=
  if (i : ℕ) + j = 0 then number 1 (profile d)
  else if (i : ℕ) + j = 1 ∧ (∑ s, d s) + 1 = Fintype.card S then
    ((Fintype.card S - 1).factorial : ℚ) / (24 * ∏ s, ((d s).factorial : ℚ))
  else 0

variable {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C}

/-- For every stable elliptic curve and arbitrary marked powers, the original class integral
agrees with all three branches of the surface vertex's Hodge calculation. -/
theorem nativeMoment_eq_integral (U : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (T : TailForgetCompatible C)
    (G : GluingForgetfulCompatibility F N)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1) (dvv : PointTarget.DVVRecursion P I)
    (one : value P I 1 [1] = 1 / 24) {S : Type} [Fintype S] (h : StableArity 1 S)
    (lambdaOne : C.H 1 S) (identification : lambdaOne = ellipticBoundary N h)
    (i j : Fin 2) (d : S → ℕ) :
    nativeMoment i j d = I.integrate 1 S h
      (P.monomial 1 S h d *
        ((if i = 0 then 1 else lambdaOne) * (if j = 0 then 1 else lambdaOne))) := by
  subst lambdaOne
  have zero := initial_zero P I (by decide : Fintype.card (Option Bool) = 3) tailStable vol
  fin_cases i <;> fin_cases j
  · change number 1 (profile d) = I.integrate 1 S h (P.monomial 1 S h d * (1 * 1))
    simpa only [mul_one, PointTarget.intersectionNumber_of_stable P I 1 S h] using
      number_profile_eq_intersectionNumber P I dvv zero one 1 d
  · change (if (1 : ℕ) = 1 ∧ (∑ s, d s) + 1 = Fintype.card S then
        ((Fintype.card S - 1).factorial : ℚ) / (24 * ∏ s, ((d s).factorial : ℚ)) else 0) =
      I.integrate 1 S h (P.monomial 1 S h d * (1 * ellipticBoundary N h))
    simpa only [true_and, one_mul, eq_self] using (integral U F N P K hK T vol h d).symm
  · change (if (1 : ℕ) = 1 ∧ (∑ s, d s) + 1 = Fintype.card S then
        ((Fintype.card S - 1).factorial : ℚ) / (24 * ∏ s, ((d s).factorial : ℚ)) else 0) =
      I.integrate 1 S h (P.monomial 1 S h d * (ellipticBoundary N h * 1))
    simpa only [true_and, mul_one, eq_self] using (integral U F N P K hK T vol h d).symm
  · change 0 = I.integrate 1 S h
      (P.monomial 1 S h d * (ellipticBoundary N h * ellipticBoundary N h))
    rw [← pow_two, square_zero F N G h, mul_zero, map_zero]

end AxiomaticGW.GKM.EllipticHodge
