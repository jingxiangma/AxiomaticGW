/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.TwoPointCalibration
public import AxiomaticGW.Surfaces.DescendantStabilization
public import AxiomaticGW.Surfaces.GenusZeroReconstruction

/-!
# Two-point calibration for the fixed surfaces

All tail coefficients use the existing terminating unstable-arity reduction.
Their stable descendant callback is still required. At inverse-loop power
one the correlators are primary, so the established genus-zero reconstruction
already supplies their exact matrices from the original finite seeds.

Rows are output coordinates and columns are input states. The inverse metric
uses the existing dual labels and negative exceptional weights. The virtual
dimension bounds the inverse-loop degree at each full curve class.
-/

@[expose] public section

namespace AxiomaticGW
namespace SurfaceBasisLabel

/-- The coordinate of a state in the existing unit/divisor/point basis. -/
def coordinate {X : SurfaceTarget} : SurfaceBasisLabel X → SurfaceCohomology X.blowups → ℚ
  | .unit, v => v.1
  | .hyperplane, v => v.2.1.1
  | .exceptional i, v => v.2.1.2 i
  | .point, v => v.2.2

/-- Raising the node index extracts the correct signed output coordinate. -/
theorem coordinate_eq_pairing {X : SurfaceTarget} (a : SurfaceBasisLabel X)
    (v : SurfaceCohomology X.blowups) :
    a.coordinate v = a.inverseWeight *
      (SurfaceCohomology.frobenius X.blowups).pairing.form a.dual.value v := by
  rw [(SurfaceCohomology.frobenius X.blowups).pairing.isSymm.eq]
  change a.coordinate v = a.inverseWeight *
    tracePairing (SurfaceCohomology.counit X.blowups) v a.dual.value
  cases a <;> simp only [coordinate, inverseWeight, dual, value,
    SurfaceCohomology.tracePairing_counit_point, SurfaceCohomology.tracePairing_counit_one,
    SurfaceCohomology.tracePairing_counit_hyperplane,
    SurfaceCohomology.tracePairing_counit_exceptional, one_mul, neg_one_mul, neg_neg]

end SurfaceBasisLabel

namespace SurfaceDescendant
open SurfaceCohomology

/-- Compute a paired calibration coefficient from supplied stable genus-zero descendants.
The power-zero metric is a calibration convention, not an unstable GW invariant. -/
def pairedCalibrationValue (X : SurfaceTarget)
    (stableValues : ∀ (_beta : X.Curve) (S : Type) [Fintype S] [DecidableEq S],
      StableArity 0 S → (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ) :
    ℕ → X.Curve → SurfaceCohomology X.blowups → SurfaceCohomology X.blowups → ℚ
  | 0, beta, x, y => if beta = 0 then counit X.blowups (x * y) else 0
  | m + 1, beta, x, y =>
      stabilizedValue X 0 beta (stableValues beta) (Fin 2) ![0, m] ![x, y]

/-- Finite operator matrix with the established signed inverse metric. -/
def calibrationMatrix (X : SurfaceTarget)
    (stableValues : ∀ (_beta : X.Curve) (S : Type) [Fintype S] [DecidableEq S],
      StableArity 0 S → (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ)
    (power : ℕ) (beta : X.Curve) : Matrix (SurfaceBasisLabel X) (SurfaceBasisLabel X) ℚ :=
  fun row col ↦ row.inverseWeight *
    pairedCalibrationValue X stableValues power beta row.dual.value col.value

/-- The first inverse-loop coefficient requires only the proved primary reconstruction. -/
def firstCalibrationMatrix (X : SurfaceTarget) (beta : X.Curve) :
    Matrix (SurfaceBasisLabel X) (SurfaceBasisLabel X) ℚ :=
  fun row col ↦ row.inverseWeight * SurfaceGenusZero.primaryValue X beta
    ((Finset.univ : Finset (Fin 2)).val.map (![row.dual, col] : Fin 2 → SurfaceBasisLabel X))

/-- Two primary inputs leave no first-coefficient contribution above energy three. -/
theorem firstCalibrationMatrix_eq_zero_of_three_lt (X : SurfaceTarget) (beta : X.Curve)
    (hbeta : 3 < X.effective.energy beta) : firstCalibrationMatrix X beta = 0 := by
  have hn : beta ≠ 0 := by
    intro hb
    subst beta
    rw [map_zero] at hbeta
    omega
  funext row col
  unfold firstCalibrationMatrix SurfaceGenusZero.primaryValue
  rw [if_neg hn]
  have hc := Multiset.count_le_card
    (SurfaceBasisLabel.point : SurfaceBasisLabel X)
    ((Finset.univ : Finset (Fin 2)).val.map (![row.dual, col] : Fin 2 → SurfaceBasisLabel X))
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin] at hc
  rw [if_neg (by omega), mul_zero]
  rfl

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- The computed paired value agrees with the actual two-point calibration coefficient. -/
theorem pairedCalibrationValue_eq (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (stableValues : ∀ (_beta : X.Curve) (S : Type) [Fintype S] [DecidableEq S],
      StableArity 0 S → (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ)
    (hstable : ∀ beta (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 0 S)
      (k : S → ℕ) (a : S → SurfaceCohomology X.blowups),
      stableValues beta S h k a = M.invariant I 0 S h beta k a)
    (power : ℕ) (beta : X.Curve) (x y : SurfaceCohomology X.blowups) :
    pairedCalibrationValue X stableValues power beta x y =
      Omega.pairing.form x (U.calibrationCoefficient power beta y) := by
  cases power with
  | zero =>
      by_cases hb : beta = 0
      · subst beta
        rw [pairedCalibrationValue, if_pos rfl, U.calibrationCoefficient_constant,
          LinearMap.id_apply, T.pairing_eq, CommFrobeniusAlgebra.pairing_apply]
        rfl
      · rw [pairedCalibrationValue, if_neg hb, U.calibrationCoefficient_zero_power beta hb,
          LinearMap.zero_apply, map_zero]
  | succ m =>
      rw [pairedCalibrationValue, U.calibrationCoefficient_pairing]
      exact stabilizedValue_eq_invariant U T laws H hpair 0 beta
        (stableValues beta) (hstable beta) (Fin 2) ![0, m] ![x, y]

/-- Every computed matrix entry is the corresponding coordinate of the actual operator. -/
theorem calibrationMatrix_eq (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (stableValues : ∀ (_beta : X.Curve) (S : Type) [Fintype S] [DecidableEq S],
      StableArity 0 S → (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ)
    (hstable : ∀ beta (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 0 S)
      (k : S → ℕ) (a : S → SurfaceCohomology X.blowups),
      stableValues beta S h k a = M.invariant I 0 S h beta k a)
    (power : ℕ) (beta : X.Curve) (row col : SurfaceBasisLabel X) :
    calibrationMatrix X stableValues power beta row col =
      row.coordinate (U.calibrationCoefficient power beta col.value) := by
  rw [calibrationMatrix, pairedCalibrationValue_eq U T laws H hpair stableValues hstable,
    SurfaceBasisLabel.coordinate_eq_pairing, T.pairing_eq]

/-- The dimension rule gives finite inverse-loop support at each full effective class. -/
theorem calibrationCoefficient_eq_zero_of_high_power (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (m : ℕ) (beta : X.Curve)
    (hm : X.effective.energy beta + 1 < m) : U.calibrationCoefficient (m + 1) beta = 0 := by
  let b := (basis X.blowups).reindex (SurfaceBasisLabel.indexEquiv X).symm
  have hb (a : SurfaceBasisLabel X) : b a = a.value := by
    cases a <;> simp only [b, Module.Basis.reindex_apply, Equiv.symm_symm,
      SurfaceBasisLabel.indexEquiv, Equiv.coe_fn_mk, SurfaceBasisLabel.value,
      basis_unit, basis_hyperplane, basis_exceptional, basis_point]
  have hz : U.invariantMap 0 (Fin 2) beta ![0, m] = 0 := by
    apply Module.Basis.ext_multilinear (fun _ ↦ b)
    intro a
    simp only [hb, U.invariantMap_apply, zero_apply]
    apply U.invariant_eq_zero_of_degree_ne 0 (Fin 2) beta ![0, m]
      (fun i ↦ (a i).codimension) (fun i ↦ (a i).value)
    · intro i
      rw [T.degree_eq]
      exact (a i).value_mem_degree
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        zero_add, Nat.cast_add, T.dimension_eq, T.c1Degree_eq,
        Fintype.card_fin, GWVirtualDimension, SurfaceTarget.c1Degree,
        AddMonoidHom.coe_comp, Function.comp_apply,
        Nat.cast_ofNat, Nat.cast_zero, sub_zero, mul_one]
      change ((a 0).codimension : ℤ) + ((a 1).codimension : ℤ) + (m : ℤ) ≠
        (2 - 3) + (X.effective.energy beta : ℤ) + 2
      omega
  rw [UnstableDescendantConventions.calibrationCoefficient, hz,
    Omega.pairing.raiseTwoPoint_zero]

/-- Stable genus-zero descendants determine every calibration coefficient; no extra tail
seed family remains after the existing arity reduction. -/
theorem calibrationCoefficient_eq_of_stable_eq
    {M₁ M₂ : StableMapDescendants Omega}
    (U₁ : UnstableDescendantConventions M₁ I) (U₂ : UnstableDescendantConventions M₂ I)
    (T : SurfaceTheoryIdentification X Omega)
    (laws₁ : DescendantStringDilatonLaws M₁ I) (laws₂ : DescendantStringDilatonLaws M₂ I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L₁ : DescendantDivisorLaw M₁ I A} {L₂ : DescendantDivisorLaw M₂ I A}
    (H₁ : FullDescendantDivisorLaw U₁ L₁) (H₂ : FullDescendantDivisorLaw U₂ L₂)
    (hpair : T.DivisorPairingCompatible A) (power : ℕ) (beta : X.Curve)
    (hstable : ∀ (S : Type) [Fintype S] (h : StableArity 0 S)
      (k : S → ℕ) (a : S → SurfaceCohomology X.blowups),
      M₁.invariant I 0 S h beta k a = M₂.invariant I 0 S h beta k a) :
    U₁.calibrationCoefficient power beta = U₂.calibrationCoefficient power beta := by
  cases power with
  | zero => rfl
  | succ m =>
      ext y
      apply Omega.pairing.toDual.injective
      ext x
      rw [Omega.pairing.toDual_apply, Omega.pairing.toDual_apply,
        Omega.pairing.isSymm.eq _ x, Omega.pairing.isSymm.eq _ x,
        U₁.calibrationCoefficient_pairing, U₂.calibrationCoefficient_pairing]
      exact invariant_eq_of_stable_eq U₁ U₂ T laws₁ laws₂ H₁ H₂ hpair 0 beta hstable
        (Fin 2) ![0, m] ![x, y]

section FirstCoefficient
variable (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (H : GluingForgetfulCompatibility F N)
  (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
  (hboundary : WDVV.BoundaryClassesEqual F)
  (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)
  (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
  (U : UnstableDescendantConventions M I) (laws : DescendantStringDilatonLaws M I)
  {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
  {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible Adiv)

include H hsource hboundary p hp P T laws Hdiv hpair

/-- The complete first coefficient matrix follows from the original WDVV proof and finite
line/exceptional seeds, with no descendant reconstruction hypothesis. -/
theorem firstCalibrationMatrix_eq
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (row col : SurfaceBasisLabel X) :
    firstCalibrationMatrix X beta row col =
      row.coordinate (U.calibrationCoefficient 1 beta col.value) := by
  rw [firstCalibrationMatrix, SurfaceGenusZero.primaryValue_eq_eval A I F N H
    hsource hboundary p hp Omega P T U laws Hdiv hpair hline hE houtput,
    SurfaceBasisLabel.coordinate_eq_pairing, ← T.pairing_eq,
    U.calibrationCoefficient_pairing, ← SurfacePrimary.eval_labels]
  congr 1
  congr 1
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

end FirstCoefficient
end SurfaceDescendant
end AxiomaticGW
