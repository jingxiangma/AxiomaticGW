/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.SurfaceLocalizationEdge

/-! # Nonvanishing of normal weights for independent surface characters -/

@[expose] public noncomputable section
namespace AxiomaticGW.GKM.SurfaceLocalizationEdge
open CurveConventionCertificate EquivariantCoefficients

/-- Test the two integral directions before any fraction-field division. -/
def Transverse (w n : Fin 2 → ℤ) : Prop := n 0 * w 1 ≠ n 1 * w 0

/-- Evaluating the numerator on a covector perpendicular to the tangent kills every
rational multiple of that tangent and detects the normal determinant. -/
theorem transverse_weight (w n : Fin 2 → ℤ) (h : Transverse w n) (q : ℚ) :
    character n - (q : Coefficient) * character w ≠ 0 := by
  let p (a : Fin 2 → ℤ) : Polynomial :=
    MvPolynomial.C (a 0 : ℚ) * MvPolynomial.X 0 + MvPolynomial.C (a 1 : ℚ) * MvPolynomial.X 1
  have hp (a : Fin 2 → ℤ) : embed (p a) = character a := by
    simp only [p, character, map_add, map_mul, embed_C, Rat.cast_intCast, embed_X_zero, embed_X_one]
  have hn := embed_ne_zero_of_eval (p n - MvPolynomial.C q * p w)
    ![(w 1 : ℚ), -(w 0 : ℚ)] (by
      simp only [p, map_sub, map_mul, map_add, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', RingHom.id_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      have det : (n 0 : ℚ) * (w 1 : ℚ) ≠ (n 1 : ℚ) * (w 0 : ℚ) := by
        exact_mod_cast h
      convert sub_ne_zero.mpr det using 1
      ring)
  simpa only [map_sub, map_mul, hp, embed_C] using hn

/-- Every signed-degree normal factor and tangent denominator exists over the original
two-character field if the tangent and transverse normal are independent. -/
theorem atEdge_isSome {X : SurfaceTarget} {v e : ℕ} (t : Tables X v e) (i : Fin e)
    (d : ℕ+) (ht : Transverse (t.edges i).weight
      (edgeWeight t (t.edges i).source (t.edges i).normalSource)) : (atEdge? t i d).isSome := by
  classical
  let w := (t.edges i).weight
  let n := edgeWeight t (t.edges i).source (t.edges i).normalSource
  have h : Transverse w n := ht
  have rev : Transverse n w := by
    intro he
    exact h ((mul_comm _ _).trans (he.symm.trans (mul_comm _ _)))
  have hw : character w ≠ 0 := by
    simpa only [Rat.cast_zero, zero_mul, sub_zero] using transverse_weight n w rev 0
  change (factor? d (character w) (character n) (t.edges i).normalDegree).isSome
  have hf : (d.val.factorial : Coefficient) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [factor?, hw, hf, or_self, if_false]
  cases k : (d.val : ℤ) * (t.edges i).normalDegree with
  | ofNat b =>
    have nz (j : Fin (b+1)) :
        character n - (j.val : Coefficient) * (character w / (d.val : Coefficient)) ≠ 0 := by
      have hz := transverse_weight w n h ((j.val : ℚ) / (d.val : ℚ))
      rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast] at hz
      rwa [div_mul_eq_mul_div, mul_div_assoc] at hz
    have hp := Finset.prod_ne_zero_iff.mpr (fun j (_ : j ∈ Finset.univ) ↦ nz j)
    simp only [normal?, hp, if_false]
    rfl
  | negSucc b => rfl

end AxiomaticGW.GKM.SurfaceLocalizationEdge
