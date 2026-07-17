/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.Novikov
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Tactic.Ring

/-!
# Descendant variables

The variable `(k, alpha)` records the insertion `tau_k(phi_alpha)`. Formal
partial differentiation is defined coefficientwise on multivariable power
series.
-/

@[expose] public section

namespace AxiomaticGW

/-- Index of a descendant variable: cotangent power and state-space basis
label. -/
abbrev DescendantVariable (BasisIndex : Type*) := ℕ × BasisIndex

/-- A Novikov-valued formal potential in a chosen variable type. -/
abbrev FormalPotential {B : Type*} [AddCancelCommMonoid B]
    (D : EffectiveCurveMonoid B) (Vars R : Type*) :=
  MvPowerSeries Vars (NovikovSeries D R)

namespace MvPowerSeries

variable {Vars R : Type*} [CommRing R]

/-- Formal partial derivative with respect to one multivariable-series
variable. -/
noncomputable def pderiv (v : Vars) :
    MvPowerSeries Vars R →ₗ[R] MvPowerSeries Vars R where
  toFun f n := (n v + 1) • f (n + Finsupp.single v 1)
  map_add' f g := by
    ext n
    change (n v + 1) •
        (f (n + Finsupp.single v 1) + g (n + Finsupp.single v 1)) =
      (n v + 1) • f (n + Finsupp.single v 1) +
        (n v + 1) • g (n + Finsupp.single v 1)
    exact nsmul_add _ _ _
  map_smul' r f := by
    ext n
    change (n v + 1) • (r * f (n + Finsupp.single v 1)) =
      r * ((n v + 1) • f (n + Finsupp.single v 1))
    simp only [nsmul_eq_mul]
    ring

@[simp]
theorem pderiv_apply (v : Vars) (f : MvPowerSeries Vars R)
    (n : Vars →₀ ℕ) :
    pderiv v f n = (n v + 1) • f (n + Finsupp.single v 1) := rfl

@[simp]
theorem pderiv_zero (v : Vars) : pderiv v (0 : MvPowerSeries Vars R) = 0 :=
  map_zero (pderiv v)

@[simp]
theorem pderiv_add (v : Vars) (f g : MvPowerSeries Vars R) :
    pderiv v (f + g) = pderiv v f + pderiv v g :=
  map_add (pderiv v) f g

/-- Partial derivatives in distinct formal variables commute. -/
theorem pderiv_comm {v w : Vars} (h : v ≠ w)
    (f : MvPowerSeries Vars R) :
    pderiv v (pderiv w f) = pderiv w (pderiv v f) := by
  apply funext
  intro n
  change (n v + 1) •
      ((n + (Finsupp.single v 1 : Vars →₀ ℕ)) w + 1) •
        f (n + Finsupp.single v 1 + Finsupp.single w 1) =
    (n w + 1) •
      ((n + (Finsupp.single w 1 : Vars →₀ ℕ)) v + 1) •
        f (n + Finsupp.single w 1 + Finsupp.single v 1)
  have hindex : n + (Finsupp.single v 1 : Vars →₀ ℕ) + Finsupp.single w 1 =
      n + Finsupp.single w 1 + Finsupp.single v 1 := by
    ac_rfl
  rw [hindex]
  simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne h,
    Finsupp.single_eq_of_ne (Ne.symm h), add_zero, nsmul_eq_mul]
  ring

end MvPowerSeries

end AxiomaticGW
