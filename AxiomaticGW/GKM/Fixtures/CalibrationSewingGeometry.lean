/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.CalibrationSewing

/-! # Geometric interpretation of the finite nonprimitive calibration sewing rows

Only the toric metric and native two-point descendants enter. Zero curve
and zero loop terms follow from the unstable descendant conventions.
-/

@[expose] public section
namespace AxiomaticGW.GKM.CalibrationSewing
open EquivariantCoefficients Matrix EquivariantCalibrationReplay
open BlowupQuantumIdempotents (Index Direction)
open SmallQuantumGeneratorComparison (generator)
open SemisimpleCalibration (raised descendant_calibration)
noncomputable section

variable {X : SurfaceTarget} {C : StableCurveCohomology Coefficient}
  {Ω : GromovWittenTheory Coefficient (Index X → Coefficient) X.Curve X.effective C}
  {M : StableMapDescendants Ω} {I : StableCurveIntegration C}
  (U : UnstableDescendantConventions M I)
  (hmetric : ∀ i a, Ω.pairing.form (Pi.single i 1) a = ((tables X).metric *ᵥ a) i)
  (htwo : ∀ (m : Fin 3) (d : Direction X) i j,
    U.invariant 0 (Fin 2) (generator X d) ![0, m.val] ![Pi.single i 1, Pi.single j 1] =
      paired X m d i j)

include hmetric htwo in
private theorem interior_pair (k l : Fin 3) (c d : Direction X) (i j : Index X) :
    Ω.pairing.form (U.calibrationCoefficient (k.val+1) (generator X c) (Pi.single i 1))
      (U.calibrationCoefficient (l.val+1) (generator X d) (Pi.single j 1)) =
      ((paired X k c).transpose * ((tables X).inverseMetric * paired X l d)) i j := by
  rw [descendant_calibration U hmetric htwo l d j]
  have hc : (raised X l d).col j = ∑ t, raised X l d t j • Pi.single t 1 := by
    funext t
    simp [Matrix.col, Finset.sum_apply, Pi.single_apply]
  rw [hc, map_sum, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_smul, Ω.pairing.isSymm.eq _ (Pi.single t 1), U.calibrationCoefficient_pairing, htwo]
  exact mul_comm _ _

private abbrev Key (X : SurfaceTarget) := (ℕ × ℕ) × X.Curve × X.Curve

private def keyOf {X : SurfaceTarget} (c : Direction X × Direction X) (k : Fin 3 × Fin 3) :
    Key X := ((k.1.val+1, k.2.val+1), generator X c.1, generator X c.2)

private def middleKeys {X : SurfaceTarget} (s : Row X) : List (Key X) :=
  s.cuts.flatMap (fun c ↦ s.power.cuts.map (keyOf c))

private def keys {X : SurfaceTarget} (s : Row X) : List (Key X) :=
  ((0,s.power.val), 0,s.beta) :: ((s.power.val,0),s.beta,0) :: middleKeys s

private def admissible {X : SurfaceTarget} (e : Key X) : Bool :=
  (decide (e.1.1 = 0) == decide (e.2.1 = 0)) && (decide (e.1.2 = 0) == decide (e.2.2 = 0))

private theorem key_binding (X : SurfaceTarget) (r : Fin (rowCount X)) :
    let s := row X r
    (keys s).Nodup ∧ (keys s).toFinset =
      ((Finset.HasAntidiagonal.antidiagonal s.power.val) ×ˢ (X.splittings s.beta)).filter
        (fun e ↦ admissible e = true) := by
  revert r
  cases X <;> decide +kernel

private def contribution (i j : Index X) (e : Key X) : Coefficient :=
  (-1 : Coefficient)^e.1.1 * Ω.pairing.form
    (U.calibrationCoefficient e.1.1 e.2.1 (Pi.single i 1))
    (U.calibrationCoefficient e.1.2 e.2.2 (Pi.single j 1))

private theorem inactive (p : ℕ) (b : X.Curve) (h : ¬(p = 0 ↔ b = 0)) :
    U.calibrationCoefficient p b = 0 := by
  cases p with
  | zero =>
    exact U.calibrationCoefficient_zero_power b (fun hb ↦ h ⟨fun _ ↦ hb, fun _ ↦ rfl⟩)
  | succ p =>
    have hb : b = 0 := by by_contra hn; exact h (by simp only [Nat.succ_ne_zero, hn])
    rw [hb, U.calibrationCoefficient_zero_class]

private theorem inactive_term (i j : Index X) (e : Key X) (h : admissible e ≠ true) :
    contribution U i j e = 0 := by
  by_cases h1 : e.1.1 = 0 ↔ e.2.1 = 0
  · have h2 : ¬(e.1.2 = 0 ↔ e.2.2 = 0) := by
      intro h2
      exact h (by simp [admissible, h1, h2])
    simp only [contribution, inactive U _ _ h2, LinearMap.zero_apply, map_zero, mul_zero]
  · simp only [contribution, inactive U _ _ h1, LinearMap.zero_apply, map_zero,
      LinearMap.zero_apply, mul_zero]

private theorem actual_sum (r : Fin (rowCount X)) (i j : Index X) :
    U.twoPointCalibration.symplecticCoefficient (row X r).power.val (row X r).beta
      (Pi.single i 1) (Pi.single j 1) = ((keys (row X r)).map (contribution U i j)).sum := by
  let s := row X r
  let allCuts := (Finset.HasAntidiagonal.antidiagonal s.power.val) ×ˢ X.splittings s.beta
  change (∑ p ∈ Finset.HasAntidiagonal.antidiagonal s.power.val,
    ∑ c ∈ X.effective.splittings s.beta, contribution U i j (p,c)) = _
  rw [← X.splittings_eq, ← Finset.sum_product]
  change (∑ e ∈ allCuts, contribution U i j e) = _
  have hf : (allCuts.filter (fun e ↦ admissible e = true)).sum (contribution U i j) =
      allCuts.sum (contribution U i j) := by
    apply Finset.sum_filter_of_ne
    intro e _ hn
    by_contra h
    exact hn (inactive_term U i j e h)
  rw [← hf]
  change (∑ e ∈ ((Finset.HasAntidiagonal.antidiagonal s.power.val) ×ˢ
    X.splittings s.beta).filter (fun e ↦ admissible e = true), contribution U i j e) = _
  rw [← (key_binding X r).2]
  exact List.sum_toFinset _ (key_binding X r).1

include hmetric htwo in
private theorem middle_sum (s : Row X) (i j : Index X) :
    ((middleKeys s).map (contribution U i j)).sum = interior s (tables X).inverseMetric i j := by
  have hc (c : Direction X × Direction X) (k : Fin 3 × Fin 3) :
      contribution U i j (keyOf c k) = ((-1 : Coefficient)^(k.1.val+1)) *
        ((paired X k.1 c.1).transpose * ((tables X).inverseMetric * paired X k.2 c.2)) i j := by
    unfold contribution keyOf
    rw [interior_pair U hmetric htwo]
  cases hp : s.power <;> by_cases hd : s.left = s.right <;>
    simp [middleKeys, interior, Row.cuts, Power.cuts, hp, hd, hc,
      Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, add_assoc]

include hmetric htwo in
/-- At this composite class the geometric calibration satisfies the actual coefficient
of S(-z)*S(z) on the toric basis, under identification of the metric, the primitive
two-point descendants and the single native endpoint matrix. -/
theorem descendant_symplecticCoefficient_basis (r : Fin (rowCount X))
    (hrow : ∀ i j, U.invariant 0 (Fin 2) (row X r).beta ![0, (row X r).power.val - 1]
      ![Pi.single i 1, Pi.single j 1] = endpoint X r i j) (i j : Index X) :
    U.twoPointCalibration.symplecticCoefficient (row X r).power.val (row X r).beta
      (Pi.single i 1) (Pi.single j 1) = 0 := by
  let s := row X r
  have hpow : s.power.val = (s.power.val-1)+1 := by cases h : s.power <;> rfl
  have hpair (i j : Index X) :
      Ω.pairing.form (Pi.single i 1) (U.calibrationCoefficient s.power.val s.beta (Pi.single j 1))
        = endpoint X r i j := by
    conv_lhs => rw [hpow, U.calibrationCoefficient_pairing]
    exact hrow i j
  rw [actual_sum]
  change ((keys s).map (contribution U i j)).sum = _
  simp only [keys, List.map_cons, List.sum_cons, middle_sum U hmetric htwo]
  change (-1 : Coefficient)^0 * Ω.pairing.form (U.calibrationCoefficient 0 0 (Pi.single i 1))
    (U.calibrationCoefficient s.power.val s.beta (Pi.single j 1)) +
    ((-1 : Coefficient)^s.power.val * Ω.pairing.form
      (U.calibrationCoefficient s.power.val s.beta (Pi.single i 1))
      (U.calibrationCoefficient 0 0 (Pi.single j 1)) + _) = _
  rw [U.calibrationCoefficient_constant, LinearMap.id_apply, LinearMap.id_apply,
    hpair, Ω.pairing.isSymm.eq _ (Pi.single j 1), hpair, pow_zero, one_mul, ← add_assoc]
  exact congrFun (congrFun (coefficient_zero X r) i) j

include hmetric htwo in
/-- Finite nonprimitive symplectic compatibility holds for arbitrary equivariant states. -/
theorem descendant_symplecticCoefficient (r : Fin (rowCount X))
    (hrow : ∀ i j, U.invariant 0 (Fin 2) (row X r).beta ![0, (row X r).power.val - 1]
      ![Pi.single i 1, Pi.single j 1] = endpoint X r i j) (a b : Index X → Coefficient) :
    U.twoPointCalibration.symplecticCoefficient (row X r).power.val (row X r).beta a b = 0 := by
  let s := row X r
  let form : LinearMap.BilinForm Coefficient (Index X → Coefficient) :=
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s.power.val,
      ∑ c ∈ X.effective.splittings s.beta, (-1 : Coefficient)^p.1 •
        Ω.pairing.form.compl₁₂ (U.calibrationCoefficient p.1 c.1)
          (U.calibrationCoefficient p.2 c.2)
  have hform (v w : Index X → Coefficient) : form v w =
      U.twoPointCalibration.symplecticCoefficient s.power.val s.beta v w := by
    simp only [form, TwoPointCalibration.symplecticCoefficient, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.compl₁₂_apply, smul_eq_mul]
    rfl
  have hz : form = 0 := by
    apply (Pi.basisFun Coefficient (Index X)).ext
    intro i
    apply (Pi.basisFun Coefficient (Index X)).ext
    intro j
    simpa only [Pi.basisFun_apply, hform, LinearMap.zero_apply] using
      descendant_symplecticCoefficient_basis U hmetric htwo r hrow i j
  rw [← hform, hz, LinearMap.zero_apply, LinearMap.zero_apply]

end
end AxiomaticGW.GKM.CalibrationSewing
