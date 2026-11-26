/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.CalibrationRecursion
public import AxiomaticGW.Surfaces.TwoPointCalibration
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite reconstruction of every two-point calibration coefficient

The anticanonical degree is positive at each nonzero effective class of the
three fixed surfaces. The cotangent comparison and divisor law therefore
determine the next inverse-loop coefficient from the previous one. All primary
three-point factors reduce to the first calibration coefficient, except for
the classical cup product at degree zero. The matrix recursion needs neither
a stable-descendant callback nor additional numerical seeds.

Soundness still requires the explicit virtual intersection, stabilization,
and rational-tail inputs; no stable-map moduli construction is asserted here.
-/

@[expose] public section

namespace AxiomaticGW
namespace SurfaceBasisLabel

/-- The existing surface basis, indexed by the public query labels. -/
noncomputable def labelBasis (X : SurfaceTarget) :
    Module.Basis (SurfaceBasisLabel X) ℚ (SurfaceCohomology X.blowups) :=
  (SurfaceCohomology.basis X.blowups).reindex (indexEquiv X).symm

theorem labelBasis_apply {X : SurfaceTarget} (a : SurfaceBasisLabel X) :
    labelBasis X a = a.value := by
  cases a <;> simp only [labelBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    indexEquiv, Equiv.coe_fn_mk, value, SurfaceCohomology.basis_unit,
    SurfaceCohomology.basis_hyperplane, SurfaceCohomology.basis_exceptional,
    SurfaceCohomology.basis_point]

/-- Coordinates agree with the original basis representation, including exceptional signs. -/
theorem labelBasis_repr {X : SurfaceTarget} (a : SurfaceBasisLabel X)
    (v : SurfaceCohomology X.blowups) : (labelBasis X).repr v a = a.coordinate v := by
  cases a <;> simp only [labelBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm,
    indexEquiv, Equiv.coe_fn_mk, SurfaceCohomology.basis, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_symm, Module.Basis.prod_repr_inl,
    Module.Basis.prod_repr_inr, Module.Basis.singleton_repr, Pi.basisFun_repr,
    SurfaceCohomology.coordinates, coordinate] <;> rfl

end SurfaceBasisLabel

namespace SurfaceTarget

/-- Executable positive-tail cuts of a full effective class. -/
def positiveTailSplittings (X : SurfaceTarget) (beta : X.Curve) : Finset (X.Curve × X.Curve) :=
  (X.splittings beta).filter (fun split ↦ split.2 ≠ 0)

theorem positiveTailSplittings_eq (X : SurfaceTarget) (beta : X.Curve) :
    X.positiveTailSplittings beta = X.effective.positiveTailSplittings beta := by
  rw [positiveTailSplittings, X.splittings_eq]
  ext split
  simp only [Finset.mem_filter, X.effective.mem_splittings,
    X.effective.mem_positiveTailSplittings]

end SurfaceTarget

namespace SurfaceDescendant
open SurfaceCohomology SurfaceBasisLabel

/-- Classical multiplication by the anticanonical divisor, in the fixed basis. -/
def anticanonicalCupMatrix (X : SurfaceTarget) :
    Matrix (SurfaceBasisLabel X) (SurfaceBasisLabel X) ℚ :=
  fun row col ↦ row.coordinate ((firstChernDivisor X.blowups).val * col.value)

/-- Primary divisor insertion, obtained from the first calibration matrix by the
divisor equation at positive class and the classical cubic at zero class. -/
def anticanonicalPrimaryMatrix (X : SurfaceTarget) (beta : X.Curve) :
    Matrix (SurfaceBasisLabel X) (SurfaceBasisLabel X) ℚ :=
  if beta = 0 then anticanonicalCupMatrix X else
    (X.effective.energy beta : ℚ) • firstCalibrationMatrix X beta

/-- Terminating recursion in inverse-loop power, retaining every full curve split.
The power-zero identity is a calibration convention, not a numerical two-point value. -/
def reconstructedCalibrationMatrix (X : SurfaceTarget) :
    ℕ → X.Curve → Matrix (SurfaceBasisLabel X) (SurfaceBasisLabel X) ℚ
  | 0, beta => if beta = 0 then 1 else 0
  | 1, beta => firstCalibrationMatrix X beta
  | m + 2, beta => if beta = 0 then 0 else
      (X.effective.energy beta : ℚ)⁻¹ •
        ((∑ split ∈ X.positiveTailSplittings beta,
          anticanonicalPrimaryMatrix X split.1 * reconstructedCalibrationMatrix X (m+1) split.2) -
          reconstructedCalibrationMatrix X (m+1) beta * anticanonicalCupMatrix X)

/-- The classical matrix has precisely the standard linear-map interpretation. -/
theorem anticanonicalCupMatrix_eq (X : SurfaceTarget) :
    anticanonicalCupMatrix X = LinearMap.toMatrix (labelBasis X) (labelBasis X)
      (LinearMap.mulLeft ℚ (firstChernDivisor X.blowups).val) := by
  ext row col
  rw [LinearMap.toMatrix_apply, labelBasis_apply, labelBasis_repr]
  rfl

section Soundness
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
  (laws : DescendantStringDilatonLaws M I)
  {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
  {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible A)

include T laws H hpair

/-- Every primary main factor is already a first-coefficient or classical cup value. -/
theorem primary_anticanonical_calibration (beta : X.Curve)
    (x y : SurfaceCohomology X.blowups) :
    U.invariant 0 (Option (Fin 2)) beta 0
        (Option.casesOn · y ![(firstChernDivisor X.blowups).val,x]) =
      Omega.pairing.form x
        ((if beta = 0 then LinearMap.mulLeft ℚ (firstChernDivisor X.blowups).val else
          (X.effective.energy beta : ℚ) • U.calibrationCoefficient 1 beta) y) := by
  by_cases hb : beta = 0
  · subst beta
    rw [if_pos rfl]
    have hz : (0 : Option (Fin 2) → ℕ) = (fun _ ↦ 0) := rfl
    rw [hz, SurfacePrimary.invariant_zero_cubic U T laws (Option (Fin 2))
      (by decide +kernel)]
    simp only [Fintype.prod_option, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, LinearMap.mulLeft_apply, T.pairing_eq,
      CommFrobeniusAlgebra.pairing_apply]
    congr 1
    ring
  · rw [if_neg hb, LinearMap.smul_apply, map_smul, smul_eq_mul]
    have he := H.primary_threePoint_calibration beta hb
      (T.divisor (firstChernDivisor X.blowups)) x y
    rw [hpair, SurfaceTarget.divisorPairing_firstChernDivisor] at he
    simp only [SurfaceTheoryIdentification.divisor] at he
    exact he

/-- The derived mixed comparison gives an operator recurrence over the original
GW family. The order of the two matrix products is forced by the input marking. -/
theorem calibration_operator_scaled
    {G : StableMapIntersection U} {St : StableMapStabilization G} {P : PsiClasses C}
    (K : RationalTailIntersection G St P) (beta : X.Curve) (hb : beta ≠ 0) (m : ℕ) :
    (X.effective.energy beta : ℚ) • U.calibrationCoefficient (m+2) beta =
      (∑ split : ↥(X.effective.positiveTailSplittings beta),
        (if split.val.1 = 0 then LinearMap.mulLeft ℚ (firstChernDivisor X.blowups).val else
          (X.effective.energy split.val.1 : ℚ) • U.calibrationCoefficient 1 split.val.1) *
            U.calibrationCoefficient (m+1) split.val.2) -
        U.calibrationCoefficient (m+1) beta *
          LinearMap.mulLeft ℚ (firstChernDivisor X.blowups).val := by
  ext y
  apply Omega.pairing.toDual.injective
  ext x
  simp only [SymmetricPerfectPairing.toDual_apply]
  rw [Omega.pairing.isSymm.eq _ x, Omega.pairing.isSymm.eq _ x]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    Module.End.mul_apply, LinearMap.mulLeft_apply, map_smul, map_sub, map_sum, smul_eq_mul]
  have he := K.calibration_pairing_recursion H beta hb m
    (T.divisor (firstChernDivisor X.blowups)) x y
  rw [hpair, SurfaceTarget.divisorPairing_firstChernDivisor,
    T.divisorAction_eq_mul U laws L] at he
  have hc : (X.c1Degree beta : ℚ) = (X.effective.energy beta : ℚ) := by
    change ((X.effective.energy beta : ℤ) : ℚ) = _
    exact Int.cast_natCast _
  rw [hc] at he
  simp only [SurfaceTheoryIdentification.divisor] at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro split _
  exact primary_anticanonical_calibration U T laws H hpair _ x _

/-- An identified first coefficient determines every higher matrix by the derived
geometric recurrence. The final theorem below discharges that identification
using the original WDVV reconstruction and finite seeds. -/
theorem reconstructedCalibrationMatrix_eq_of_first
    {G : StableMapIntersection U} {St : StableMapStabilization G} {P : PsiClasses C}
    (K : RationalTailIntersection G St P)
    (hfirst : ∀ beta row col, firstCalibrationMatrix X beta row col =
      row.coordinate (U.calibrationCoefficient 1 beta col.value))
    (power : ℕ) (beta : X.Curve) :
    reconstructedCalibrationMatrix X power beta =
      LinearMap.toMatrix (labelBasis X) (labelBasis X) (U.calibrationCoefficient power beta) := by
  have hf (b : X.Curve) : firstCalibrationMatrix X b =
      LinearMap.toMatrix (labelBasis X) (labelBasis X) (U.calibrationCoefficient 1 b) := by
    ext row col
    rw [LinearMap.toMatrix_apply, labelBasis_apply, labelBasis_repr]
    exact hfirst b row col
  have hc (b : X.Curve) : anticanonicalPrimaryMatrix X b =
      LinearMap.toMatrix (labelBasis X) (labelBasis X)
        (if b = 0 then LinearMap.mulLeft ℚ (firstChernDivisor X.blowups).val else
          (X.effective.energy b : ℚ) • U.calibrationCoefficient 1 b) := by
    by_cases hb : b = 0
    · rw [anticanonicalPrimaryMatrix, if_pos hb, if_pos hb, anticanonicalCupMatrix_eq]
    · rw [anticanonicalPrimaryMatrix, if_neg hb, if_neg hb, map_smul, hf]
  induction power using Nat.twoStepInduction generalizing beta with
  | zero =>
      by_cases hb : beta = 0
      · subst beta
        rw [reconstructedCalibrationMatrix, if_pos rfl, U.calibrationCoefficient_constant,
          LinearMap.toMatrix_id]
      · rw [reconstructedCalibrationMatrix, if_neg hb,
          U.calibrationCoefficient_zero_power beta hb, map_zero]
  | one => exact hf beta
  | more m _ ih =>
      by_cases hb : beta = 0
      · subst beta
        rw [reconstructedCalibrationMatrix, if_pos rfl, U.calibrationCoefficient_zero_class,
          map_zero]
      · have hn : (X.effective.energy beta : ℚ) ≠ 0 := by
          exact_mod_cast (X.effective.energy_eq_zero_iff beta).not.mpr hb
        have he := calibration_operator_scaled U T laws H hpair K beta hb m
        have hi := congrArg (fun f ↦ (X.effective.energy beta : ℚ)⁻¹ • f) he
        rw [inv_smul_smul₀ hn] at hi
        rw [reconstructedCalibrationMatrix, if_neg hb, hi, map_smul, map_sub, map_sum]
        congr 1
        congr 1
        · rw [X.positiveTailSplittings_eq, ← Finset.sum_coe_sort]
          apply Finset.sum_congr rfl
          intro split _
          rw [hc, ih, LinearMap.toMatrix_mul]
        · rw [ih, anticanonicalCupMatrix_eq, LinearMap.toMatrix_mul]

/-- Every coefficient is reconstructed from the original WDVV geometric input,
the finite genus-zero seed package and primitive rational-tail geometry.
No stable-descendant values or higher calibration coefficients are inputs. -/
theorem reconstructedCalibrationMatrix_eq
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Fsep : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (J : GluingForgetfulCompatibility Fsep N)
    (hsource : ∀ i, (WDVV.expression i).Compatible Z Fsep N)
    (hboundary : WDVV.BoundaryClassesEqual Fsep)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)
    (P : PsiClasses C)
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z Fsep N)
    {G : StableMapIntersection U} {St : StableMapStabilization G}
    (K : RationalTailIntersection G St P) (power : ℕ) (beta : X.Curve)
    (row col : SurfaceBasisLabel X) :
    reconstructedCalibrationMatrix X power beta row col =
      row.coordinate (U.calibrationCoefficient power beta col.value) := by
  have he := reconstructedCalibrationMatrix_eq_of_first U T laws H hpair K
    (firstCalibrationMatrix_eq Z Fsep N J hsource hboundary p hp P T U laws H hpair
      hline hE houtput) power beta
  rw [he, LinearMap.toMatrix_apply, labelBasis_apply, labelBasis_repr]

end Soundness

end SurfaceDescendant
end AxiomaticGW
