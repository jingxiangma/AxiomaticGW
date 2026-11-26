/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.EquivariantCoefficients
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Homogeneous equivariant localization sums regular at zero

Homogeneity may be visible in a fraction whose denominator vanishes at the origin.
A separate regular representative determines its polynomial, including its full
two-character value when the equivariant degree is zero.
-/

public section
namespace AxiomaticGW.GKM.EquivariantCoefficients
open MvPolynomial

private theorem component_mul (p b : Polynomial) {m : ℕ} (hb : b.IsHomogeneous m) (k : ℕ) :
    homogeneousComponent (k + m) (p * b) = homogeneousComponent k p * b := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have h := isHomogeneous_monomial (σ := Fin 2) (d := d) c rfl
    rw [homogeneousComponent_of_mem (h.mul hb), homogeneousComponent_of_mem h]
    simp only [Nat.add_right_cancel_iff]
    split <;> simp only [zero_mul]
  | add p q hp hq => rw [add_mul, map_add, hp, hq, map_add, add_mul]

private theorem coeff_zero (d : Polynomial) : MvPolynomial.coeff 0 d = atZero d := by
  change _ = MvPolynomial.eval (0 : Fin 2 → ℚ) d
  rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]

private theorem cross {a b n d : Polynomial} (hb : embed b ≠ 0) (hd : atZero d ≠ 0)
    (h : embed a / embed b = embed n / embed d) : n * b = d * a := by
  have hc := (div_eq_div_iff hb (embed_ne_zero_of_atZero d hd)).mp h
  apply IsFractionRing.injective Polynomial Coefficient
  simpa only [map_mul, mul_comm] using hc.symm

/-- A homogeneous fraction of excess degree k regular at the origin is a polynomial.
It is obtained from the degree-k component of any regular numerator and the constant
coefficient of its denominator. The homogeneous denominator itself may vanish at zero. -/
theorem homogeneous_regular_polynomial {a b n d : Polynomial} {m k : ℕ}
    (ha : a.IsHomogeneous (k + m)) (hb : b.IsHomogeneous m) (hb₀ : embed b ≠ 0)
    (hd : atZero d ≠ 0) (he : embed a / embed b = embed n / embed d) :
    let p := C (atZero d)⁻¹ * homogeneousComponent k n
    p.IsHomogeneous k ∧ embed a / embed b = embed p := by
  dsimp only
  constructor
  · simpa only [zero_add] using
      (isHomogeneous_C (σ := Fin 2) (atZero d)⁻¹).mul (homogeneousComponent_isHomogeneous k n)
  · have hc := congrArg (homogeneousComponent (k + m)) (cross hb₀ hd he)
    have hz := component_mul d a ha 0
    rw [zero_add] at hz
    rw [component_mul n b hb k, hz, homogeneousComponent_zero, coeff_zero] at hc
    have hh := congrArg (fun p : Polynomial ↦ C (atZero d)⁻¹ * p) hc
    rw [← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd, map_one, one_mul] at hh
    apply (div_eq_iff hb₀).mpr
    simpa only [map_mul] using congrArg embed hh.symm

/-- If total insertion codimension equals virtual dimension, a homogeneous localization
sum has weight zero. Its regular ordinary specialization then determines the entire fraction. -/
theorem eq_constant_of_homogeneous {a b : Polynomial} {m : ℕ} {q : ℚ}
    (ha : a.IsHomogeneous m) (hb : b.IsHomogeneous m) (hb₀ : embed b ≠ 0)
    (hs : Specializes (embed a / embed b) q) : embed a / embed b = (q : Coefficient) := by
  obtain ⟨n, d, hd, he, hq⟩ := hs
  have h := (homogeneous_regular_polynomial (k := 0) (by simpa only [zero_add] using ha)
    hb hb₀ hd he.symm).2
  rw [homogeneousComponent_zero, coeff_zero, ← map_mul, embed_C,
    mul_comm, ← div_eq_mul_inv, hq] at h
  exact h

/-- A homogeneous fraction of strictly negative degree vanishes if it is regular at the
origin. Individual fixed-locus contributions with a genuine pole need not vanish. -/
theorem eq_zero_of_negative_degree {a b : Polynomial} {l m : ℕ} {q : ℚ}
    (ha : a.IsHomogeneous l) (hb : b.IsHomogeneous m) (hlt : l < m)
    (hb₀ : embed b ≠ 0) (hs : Specializes (embed a / embed b) q) : a = 0 := by
  obtain ⟨n, d, hd, he, _⟩ := hs
  have below (p : Polynomial) : homogeneousComponent l (p * b) = 0 := by
    induction p using MvPolynomial.induction_on' with
    | monomial s c =>
      have h := isHomogeneous_monomial (σ := Fin 2) (d := s) c rfl
      rw [homogeneousComponent_of_mem (h.mul hb), if_neg (by omega)]
    | add p r hp hr => rw [add_mul, map_add, hp, hr, add_zero]
  have h := congrArg (homogeneousComponent l) (cross hb₀ hd he.symm)
  have hz := component_mul d a ha 0
  rw [zero_add] at hz
  rw [below, hz, homogeneousComponent_zero, coeff_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (MvPolynomial.C_ne_zero.mpr hd)

end AxiomaticGW.GKM.EquivariantCoefficients
