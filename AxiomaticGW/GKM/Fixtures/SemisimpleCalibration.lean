/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.EquivariantCalibrationReplay
public import AxiomaticGW.GKM.Fixtures.PlaneQuantumPairs
public import AxiomaticGW.GKM.CalibrationSpectrum
public import AxiomaticGW.GW.Descendants.TwoPointCalibration

/-!
# Semisimple calibration transition at primitive Novikov degree

The primaries and one- and two-psi descendants determine the first three
inverse-loop coefficients with the first marking used as the node. The
primitive-class anticanonical commutator has a rational solution at infinity.
At distinct classical tangent sums its constant term near zero is the actual
infinitesimal primitive projector displacement. Positive-loop diagonal gauge
and the all-genus geometric action require additional data.
-/

@[expose] public section
namespace AxiomaticGW.GKM.SemisimpleCalibration
open EquivariantCoefficients Matrix EquivariantCalibrationReplay FirstOrderFixedPoints
open CalibrationSpectrum
open BlowupQuantumIdempotents (Index Direction Presentation)
open SmallQuantumGeneratorComparison (tensor generator)
noncomputable section

def presentation : (X : SurfaceTarget) → Presentation X
  | .plane => PlaneQuantumPairs.presentation
  | .hirzebruchOne => BlowupQuantumIdempotents.OneBlowup.presentation
  | .blowupTwo => BlowupQuantumIdempotents.TwoBlowups.presentation

theorem request_eq (X : SurfaceTarget) : (presentation X).request = request X := by cases X <;> rfl

/-- Native ordered paired input evaluated on two classical fixed-point idempotents. -/
def fixedPaired (X : SurfaceTarget) (m : Fin 3) (d : Direction X) :
    Matrix (Index X) (Index X) Coefficient := pull (tables X).inverse (paired X m d)

/-- Raising the node at point i multiplies by its tangent Euler factor. The retained
marking j is the column. This is the coefficient of qᵈ z^(-(m + 1)). -/
def fixedOperator (X : SurfaceTarget) (m : Fin 3) (d : Direction X) (i j : Index X) : Coefficient :=
  (request X).euler i * fixedPaired X m d i j

theorem fixed_commutator (X : SurfaceTarget) (m : Fin 2) (d : Direction X) (i j : Index X) :
    (energy X d : Coefficient) * fixedOperator X m.succ d i j =
      ((request X).tangentSum i - (request X).tangentSum j) *
        fixedOperator X m.castSucc d i j := by
  have ha := accepted X
  have hpv : (request X).restrictions * (tables X).inverse = 1 := by
    rw [← ha.restrictions_eq, ha.restrictions_inverse]
  have hvp : (tables X).inverse * (request X).restrictions = 1 := by
    rw [← ha.restrictions_eq, ha.inverse_restrictions]
  have hc := conjugate_cup _ _ _ _ hvp hpv (cup_restrict X).1
  have h := pull_commutator _ _ _ _ _ _ hc (commutator X m d) i j
  unfold fixedOperator fixedPaired
  linear_combination (request X).euler i * h

/-- The native first coefficient in the original toric basis is exactly the
anticanonical slice of the edge presentation. -/
theorem native_divisor_form (X : SurfaceTarget) (d : Direction X) :
    (energy X d : Coefficient) • paired X 0 d =
      divisorForm (request X).restrictions (presentation X).pairs (presentation X).weights d
        (request X).tangentSum := by
  rw [← (cup_restrict X).2]
  funext i j
  rw [Matrix.smul_apply, smul_eq_mul, divisor_identity, divisorForm_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← request_eq X, (presentation X).cubic_basis]

theorem fixed_divisor_form (X : SurfaceTarget) (d : Direction X) :
    (energy X d : Coefficient) • fixedPaired X 0 d =
      divisorForm 1 (presentation X).pairs (presentation X).weights d (request X).tangentSum := by
  have ha := accepted X
  unfold fixedPaired pull
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, native_divisor_form, divisorForm_pull,
    ← ha.restrictions_eq, ha.restrictions_inverse]

/-- The fixed-state diagonalization and the independently localized first calibration
matrix have the same off-diagonal infinitesimal information. -/
theorem primary_gap (X : SurfaceTarget) (d : Direction X) (i j : Index X) (hij : i ≠ j) :
    (energy X d : Coefficient) * fixedOperator X 0 d i j =
      ((request X).tangentSum i - (request X).tangentSum j) *
      changeOfBasis (request X).euler (presentation X).pairs (presentation X).weights d
        (Pi.single j 1) i := by
  have h := congrFun (congrFun (fixed_divisor_form X d) i) j
  rw [Matrix.smul_apply, smul_eq_mul] at h
  unfold fixedOperator
  rw [mul_left_comm, h, off_diagonal _ _ _ _ _ i j hij]

/-- Anticanonical eigenvalue gap divided by the actual degree of the full generator. -/
def gap (X : SurfaceTarget) (d : Direction X) (i j : Index X) : Coefficient :=
  ((request X).tangentSum i - (request X).tangentSum j) / (energy X d : Coefficient)

private def tangent {R : Type*} [CommRing R] (u v : R) : (X : SurfaceTarget) → Index X → R
  | .plane => ![u+v, u-2*v, v-2*u]
  | .hirzebruchOne => ![u-2*v,u,v-2*u,v]
  | .blowupTwo => ![u-2*v,u,v,v-u,-u]

private theorem tangent_map {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (u v : R) (X : SurfaceTarget) (i : Index X) :
    f (tangent u v X i) = tangent (f u) (f v) X i := by
  cases X <;> fin_cases i <;> simp +decide [tangent, map_ofNat]

private theorem tangent_separates (X : SurfaceTarget) :
    ∀ i j : Index X, i ≠ j → tangent (11 : ℚ) 3 X i ≠ tangent 11 3 X j := by
  cases X <;> decide +kernel

/-- The full tangent-sum spectrum is simple over the localized field on each fixed target.
A regular substitution is used exclusively to witness nonvanishing. -/
theorem gap_ne_zero (X : SurfaceTarget) (d : Direction X) (i j : Index X) (hij : i ≠ j) :
    gap X d i j ≠ 0 := by
  have hframe : (request X).tangentSum = tangent x y X := by cases X <;> rfl
  apply div_ne_zero _ (by exact_mod_cast (energy_pos X d).ne')
  rw [hframe]
  let u : Polynomial := MvPolynomial.X 0
  let v : Polynomial := MvPolynomial.X 1
  have h := embed_ne_zero_of_eval (tangent u v X i - tangent u v X j) (![11,3] : Fin 2 → ℚ)
  simp only [map_sub, tangent_map] at h
  apply h
  simpa [u,v] using sub_ne_zero.mpr (tangent_separates X i j hij)

theorem next_entry (X : SurfaceTarget) (m : Fin 2) (d : Direction X) (i j : Index X) :
    fixedOperator X m.succ d i j = gap X d i j * fixedOperator X m.castSucc d i j := by
  have hn : (energy X d : Coefficient) ≠ 0 := by exact_mod_cast (energy_pos X d).ne'
  apply (mul_left_cancel₀ hn)
  rw [fixed_commutator]
  unfold gap
  field_simp

/-- All three source powers agree with the expansion of the same simple fraction at infinity. -/
theorem native_infinity (X : SurfaceTarget) (m : Fin 3) (d : Direction X) (i j : Index X) :
    fixedOperator X m d i j =
      infinityCoefficient (fixedOperator X 0 d i j) (gap X d i j) m.val := by
  fin_cases m
  · simp [infinityCoefficient]
  · simpa [infinityCoefficient] using next_entry X 0 d i j
  · change fixedOperator X 2 d i j = infinityCoefficient _ _ 2
    have h := next_entry X 1 d i j
    change fixedOperator X 2 d i j = gap X d i j * fixedOperator X 1 d i j at h
    rw [h]
    have h1 := next_entry X 0 d i j
    change fixedOperator X 1 d i j = gap X d i j * fixedOperator X 0 d i j at h1
    rw [h1]
    simp [infinityCoefficient, pow_two, mul_assoc]

/-- The Taylor constant is the existing lifted projector's actual full-curve coefficient,
and the linear Taylor coefficient is that displacement divided by the normalized gap. -/
theorem projector_transition (X : SurfaceTarget) (d : Direction X) (i j : Index X)
    (hij : i ≠ j) :
    let c := coeff (projector (request X).euler (presentation X).pairs
      (presentation X).weights j) d i;
    -fixedOperator X 0 d i j / gap X d i j = c ∧
    -fixedOperator X 0 d i j / (gap X d i j)^2 = c / gap X d i j := by
  have hg := gap_ne_zero X d i j hij
  dsimp only
  rw [projector_coefficient, Pi.neg_apply]
  let T := changeOfBasis (request X).euler (presentation X).pairs (presentation X).weights d
    (Pi.single j 1) i
  have hn : (energy X d : Coefficient) ≠ 0 := by exact_mod_cast (energy_pos X d).ne'
  have h : fixedOperator X 0 d i j = gap X d i j * T := by
    apply mul_left_cancel₀ hn
    rw [primary_gap _ _ _ _ hij]
    dsimp only [gap, T]
    field_simp
  change -fixedOperator X 0 d i j / gap X d i j = -T ∧ _
  rw [h]
  constructor <;> field_simp [hg]
  ring

/-- The simple-pole solution is the unique inverse-loop sequence satisfying the
primitive-degree commutator with the supplied native first coefficient. -/
theorem resolvent_unique (X : SurfaceTarget) (d : Direction X) (i j : Index X)
    (a : ℕ → Coefficient) (h0 : a 0 = fixedOperator X 0 d i j)
    (hs : ∀ m, a (m + 1) = gap X d i j * a m) :
    ∀ m, a m = infinityCoefficient (fixedOperator X 0 d i j) (gap X d i j) m := by
  intro m
  induction m with
  | zero => simpa [infinityCoefficient] using h0
  | succ m ih => rw [hs, ih, infinity_succ]

/-- At a primitive class the symplectic sewing coefficient has only one positive-degree
factor. The ordered paired matrices have the required alternating transpose signs. -/
theorem native_sewing (X : SurfaceTarget) (m : Fin 3) (d : Direction X) (i j : Index X) :
    (-1 : Coefficient)^(m.val+1) * fixedPaired X m d j i + fixedPaired X m d i j = 0 := by
  have hn : (energy X d : Coefficient) ≠ 0 := by exact_mod_cast (energy_pos X d).ne'
  have hsym : fixedPaired X 0 d j i = fixedPaired X 0 d i j := by
    apply mul_left_cancel₀ hn
    have h := fixed_divisor_form X d
    have h1 := congrFun (congrFun h j) i
    have h2 := congrFun (congrFun h i) j
    rw [Matrix.smul_apply, smul_eq_mul] at h1 h2
    rw [h1,h2]
    simp only [divisorForm, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
      mul_comm (edgeRow _ _ j)]
  have hr (a b : Index X) (k : Fin 2) :
      fixedPaired X k.succ d a b = gap X d a b * fixedPaired X k.castSucc d a b := by
    have he := (presentation X).euler_ne a
    rw [request_eq] at he
    apply mul_left_cancel₀ he
    simpa only [fixedOperator, mul_left_comm ((request X).euler a)] using next_entry X k d a b
  have hg : gap X d j i = -gap X d i j := by unfold gap; ring
  have hi : fixedPaired X 1 d j i = -fixedPaired X 1 d i j := by
    rw [show fixedPaired X 1 d j i = _ from hr j i 0,
      show fixedPaired X 1 d i j = _ from hr i j 0, hg]
    change -gap X d i j * fixedPaired X 0 d j i = -(gap X d i j * fixedPaired X 0 d i j)
    rw [hsym, neg_mul]
  fin_cases m
  · simp [hsym]
  · simp [hi]
  · change (-1 : Coefficient)^3 * fixedPaired X 2 d j i + fixedPaired X 2 d i j = 0
    rw [show fixedPaired X 2 d j i = _ from hr j i 1,
      show fixedPaired X 2 d i j = _ from hr i j 1]
    change (-1 : Coefficient)^3 * (gap X d j i * fixedPaired X 1 d j i) +
      gap X d i j * fixedPaired X 1 d i j = 0
    rw [hg, hi]
    ring

/-- At opposite nonzero gaps, the native Taylor coefficients have the metric transpose
sign required by the primitive-degree sewing equation in every loop power. -/
theorem taylor_sewing (X : SurfaceTarget) (d : Direction X) {i j : Index X} (hij : i ≠ j)
    (m : ℕ) :
    ((request X).euler j)⁻¹ * taylorCoefficient (fixedOperator X 0 d j i) (gap X d j i) m =
      (-1)^(m+1) * (((request X).euler i)⁻¹ *
        taylorCoefficient (fixedOperator X 0 d i j) (gap X d i j) m) := by
  have hsym := native_sewing X 0 d i j
  change (-1 : Coefficient)^1 * fixedPaired X 0 d j i + fixedPaired X 0 d i j = 0 at hsym
  have hpair : fixedPaired X 0 d j i = fixedPaired X 0 d i j := by linear_combination -hsym
  have hg : gap X d j i = -gap X d i j := by unfold gap; ring
  have he := (presentation X).euler_ne
  rw [request_eq] at he
  rw [hg, taylor_neg_gap]
  simp only [taylorCoefficient, fixedOperator, hpair]
  field_simp [he i, he j, gap_ne_zero X d i j hij]

/-- Raise the node using the exact accepted inverse toric metric. -/
def raised (X : SurfaceTarget) (m : Fin 3) (d : Direction X) :
    Matrix (Index X) (Index X) Coefficient :=
  (tables X).inverseMetric * paired X m d

theorem lower_raised (X : SurfaceTarget) (m : Fin 3) (d : Direction X) :
    (tables X).metric * raised X m d = paired X m d := by
  rw [raised, ← Matrix.mul_assoc, (accepted X).metric_mul_inverse, one_mul]

/-- Incoming two-point numerical identification on the toric basis suffices to identify
these rational-tail operators in the existing descendant-to-ancestor interface. -/
theorem descendant_calibration {X : SurfaceTarget} {C : StableCurveCohomology Coefficient}
    {Ω : GromovWittenTheory Coefficient (Index X → Coefficient) X.Curve X.effective C}
    {M : StableMapDescendants Ω} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I)
    (hmetric : ∀ i a, Ω.pairing.form (Pi.single i 1) a = ((tables X).metric *ᵥ a) i)
    (htwo : ∀ (m : Fin 3) (d : Direction X) i j,
      U.invariant 0 (Fin 2) (generator X d) ![0, m.val] ![Pi.single i 1, Pi.single j 1] =
        paired X m d i j) (m : Fin 3) (d : Direction X) (j : Index X) :
    U.calibrationCoefficient (m.val+1) (generator X d) (Pi.single j 1) = (raised X m d).col j := by
  apply Ω.pairing.toDual.injective
  apply (Pi.basisFun Coefficient (Index X)).ext
  intro i
  rw [Pi.basisFun_apply, Ω.pairing.toDual_apply, Ω.pairing.toDual_apply,
    Ω.pairing.isSymm.eq _ (Pi.single i 1), Ω.pairing.isSymm.eq _ (Pi.single i 1),
    U.calibrationCoefficient_pairing, htwo, hmetric]
  exact (congrFun (congrFun (lower_raised X m d) i) j).symm

/-- Sewing any linear main contribution into the actual two-marked tail evaluates it
on the source-bound raised column. -/
theorem sewing {X : SurfaceTarget} {C : StableCurveCohomology Coefficient}
    {Ω : GromovWittenTheory Coefficient (Index X → Coefficient) X.Curve X.effective C}
    {M : StableMapDescendants Ω} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I)
    (hmetric : ∀ i a, Ω.pairing.form (Pi.single i 1) a = ((tables X).metric *ᵥ a) i)
    (htwo : ∀ (m : Fin 3) (d : Direction X) i j,
      U.invariant 0 (Fin 2) (generator X d) ![0, m.val] ![Pi.single i 1, Pi.single j 1] =
        paired X m d i j) (m : Fin 3) (d : Direction X) (j : Index X)
    (ℓ : Module.Dual Coefficient (Index X → Coefficient)) :
    TensorProduct.lift (((LinearMap.mul Coefficient Coefficient).comp ℓ).compl₂
      ((SymmetricPerfectPairing.finTwoToBilin
        (U.invariantMap 0 (Fin 2) (generator X d) ![0, m.val])).flip (Pi.single j 1)))
      Ω.pairing.copairing = ℓ ((raised X m d).col j) := by
  rw [Ω.pairing.raiseTwoPoint_contract]
  exact congrArg ℓ (descendant_calibration U hmetric htwo m d j)

end
end AxiomaticGW.GKM.SemisimpleCalibration
