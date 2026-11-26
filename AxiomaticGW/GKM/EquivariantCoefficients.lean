/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Exact equivariant coefficients and regular specialization

The two additive characters are algebraically independent. Nonzero
polynomial denominators embed injectively in the fraction field. Ordinary
specialization is defined only through a representative regular at zero;
there is no evaluation homomorphism from the entire fraction field to ℚ.
Equivalent regular representatives give the same value. This permits
specializing a complete localization sum after its poles have cancelled.
-/

@[expose] public section

namespace AxiomaticGW.GKM.EquivariantCoefficients

/-- Polynomial ring on the two additive torus characters. -/
abbrev Polynomial := MvPolynomial (Fin 2) ℚ

/-- Exact coefficient field used by the pinned GKM exchange. -/
abbrev Coefficient := FractionRing Polynomial

/-- The injective polynomial embedding into its fraction field. -/
noncomputable abbrev embed : Polynomial →+* Coefficient := algebraMap Polynomial Coefficient

/-- The first additive equivariant character. -/
noncomputable def x : Coefficient := embed (MvPolynomial.X 0)

/-- The second additive equivariant character. -/
noncomputable def y : Coefficient := embed (MvPolynomial.X 1)

/-- The polynomial's first variable is the same named symbolic character. -/
theorem embed_X_zero : embed (MvPolynomial.X 0) = x := rfl

/-- The polynomial's second variable is the same named symbolic character. -/
theorem embed_X_one : embed (MvPolynomial.X 1) = y := rfl

/-- Polynomial constants retain their rational coefficient. -/
theorem embed_C (q : ℚ) : embed (MvPolynomial.C q) = (q : Coefficient) := by
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply ℚ Polynomial Coefficient]
  exact map_ratCast _ q

/-- Evaluation at zero on polynomials, rather than on the whole fraction field. -/
def atZero : Polynomial →+* ℚ := MvPolynomial.eval₂Hom (RingHom.id ℚ) 0

/-- A nonzero evaluated polynomial certifies a nonzero symbolic denominator.
The evaluation is used only to prove nonvanishing, never a symbolic identity. -/
theorem embed_ne_zero_of_eval (p : Polynomial) (a : Fin 2 → ℚ)
    (h : MvPolynomial.eval₂Hom (RingHom.id ℚ) a p ≠ 0) : embed p ≠ 0 := by
  intro hp
  have hz : p = 0 := (IsFractionRing.to_map_eq_zero_iff).mp hp
  rw [hz, map_zero] at h
  exact h rfl

/-- A regular representative of a fraction has a nonzero embedded denominator. -/
theorem embed_ne_zero_of_atZero (p : Polynomial) (h : atZero p ≠ 0) : embed p ≠ 0 :=
  embed_ne_zero_of_eval p 0 h

/-- Algebraic independence ensures the first character is nonzero. -/
theorem x_ne_zero : x ≠ 0 :=
  embed_ne_zero_of_eval (MvPolynomial.X 0) (fun _ ↦ 1) (by
    rw [MvPolynomial.eval₂Hom_X']
    exact one_ne_zero)

/-- Algebraic independence ensures the second character is nonzero. -/
theorem y_ne_zero : y ≠ 0 :=
  embed_ne_zero_of_eval (MvPolynomial.X 1) (fun _ ↦ 1) (by
    rw [MvPolynomial.eval₂Hom_X']
    exact one_ne_zero)

/-- The two independent characters have nonzero difference. -/
theorem x_sub_y_ne_zero : x - y ≠ 0 := by
  have h := embed_ne_zero_of_eval (MvPolynomial.X 0 - MvPolynomial.X 1)
    (Fin.cases 1 (fun _ ↦ 0)) (by
      rw [map_sub, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      change (1 : ℚ) - 0 ≠ 0
      rw [sub_zero]
      exact one_ne_zero)
  simpa only [map_sub, embed_X_zero, embed_X_one] using h

/-- Reversing the difference changes its sign without introducing a zero. -/
theorem y_sub_x_ne_zero : y - x ≠ 0 := by
  simpa only [neg_sub] using neg_ne_zero.mpr x_sub_y_ne_zero

/-- The reverse difference remains nonzero in additive character notation. -/
theorem neg_x_add_y_ne_zero : -x + y ≠ 0 := by
  simpa only [sub_eq_add_neg, add_comm] using y_sub_x_ne_zero

/-- The forward difference remains nonzero in additive character notation. -/
theorem neg_y_add_x_ne_zero : -y + x ≠ 0 := by
  simpa only [sub_eq_add_neg, add_comm] using x_sub_y_ne_zero

/-- Equivalent representatives that are both regular at zero specialize equally. -/
theorem regular_representatives_eq (n d n' d' : Polynomial)
    (hd : atZero d ≠ 0) (hd' : atZero d' ≠ 0)
    (h : embed n / embed d = embed n' / embed d') :
    atZero n / atZero d = atZero n' / atZero d' := by
  apply (div_eq_div_iff hd hd').mpr
  have hc := (div_eq_div_iff (embed_ne_zero_of_atZero d hd)
    (embed_ne_zero_of_atZero d' hd')).mp h
  have hp : n * d' = n' * d := (IsFractionRing.injective Polynomial Coefficient) (by
    simpa only [map_mul] using hc)
  have hz := congrArg atZero hp
  simpa only [map_mul] using hz

/-- A complete symbolic expression has an ordinary value when it has a
representative whose denominator does not vanish at zero. -/
def Specializes (f : Coefficient) (value : ℚ) : Prop :=
  ∃ n d : Polynomial, atZero d ≠ 0 ∧ embed n / embed d = f ∧
    atZero n / atZero d = value

/-- The ordinary value is independent of the chosen regular representative. -/
theorem Specializes.unique {f : Coefficient} {a b : ℚ}
    (ha : Specializes f a) (hb : Specializes f b) : a = b := by
  obtain ⟨n, d, hd, hf, hv⟩ := ha
  obtain ⟨n', d', hd', hf', hv'⟩ := hb
  exact hv.symm.trans ((regular_representatives_eq n d n' d' hd hd'
    (hf.trans hf'.symm)).trans hv')

/-- A proved polynomial expression is regular, even if its original
localization presentation contained individual terms with poles. -/
theorem specializes_of_eq_polynomial {f : Coefficient} (p : Polynomial)
    (h : f = embed p) : Specializes f (atZero p) := by
  refine ⟨p, 1, ?_, ?_, ?_⟩
  · rw [map_one]
    exact one_ne_zero
  · rw [map_one, div_one, h]
  · rw [map_one, div_one]

/-- The reciprocal of a nonzero polynomial vanishing at zero has no regular
ordinary value. In particular, a fixed-locus pole cannot be specialized alone. -/
theorem not_specializes_inverse (p : Polynomial) (hp : embed p ≠ 0)
    (hzero : atZero p = 0) (value : ℚ) : ¬Specializes ((embed p)⁻¹) value := by
  rintro ⟨n, d, hd, hf, _⟩
  have hdiv : embed n / embed d = 1 / embed p := by
    simpa only [one_div] using hf
  have hc := (div_eq_div_iff (embed_ne_zero_of_atZero d hd) hp).mp hdiv
  have hpoly : n * p = d := (IsFractionRing.injective Polynomial Coefficient) (by
    simpa only [map_mul, one_mul] using hc)
  have hz := congrArg atZero hpoly
  rw [map_mul, hzero, mul_zero] at hz
  exact hd hz.symm

end AxiomaticGW.GKM.EquivariantCoefficients
