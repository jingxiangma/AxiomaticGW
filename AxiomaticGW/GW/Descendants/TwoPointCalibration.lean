/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.Stabilization
public import AxiomaticGW.GW.Descendants.FullPotential
public import AxiomaticGW.Linear.TwoPointOperator

/-!
# Calibration coefficients from actual two-point descendants

At zero primary deformation the coefficient of `z^(-(m+1)) q^beta`
is characterized by `eta(x, S y) = <x, tau_m(y)>_(0,beta)`.
The node is the first input and has no cotangent power. Perfectness raises
that node index; this construction uses the existing full numerical family,
including positive-degree curve-unstable arities. The identity at `(0,0)` is
the calibration convention, separate from the zero degree-zero two-point
numerical convention. See Givental, arXiv:math/0108100, Section 5.

This identifies the operator once its geometric paired values are supplied;
it neither asserts a stabilization formula nor assumes symplecticity.
-/

@[expose] public section

namespace AxiomaticGW
universe u
variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

namespace UnstableDescendantConventions

/-- The coefficient of `z^-power q^beta` at zero primary deformation. -/
noncomputable def calibrationCoefficient (U : UnstableDescendantConventions M I) :
    ℕ → B → Module.End R V := by
  classical
  exact fun
    | 0, beta => if beta = 0 then LinearMap.id else 0
    | m + 1, beta => Omega.pairing.raiseTwoPoint (U.invariantMap 0 (Fin 2) beta ![0, m])

/-- The constant term at zero curve class is the identity. -/
theorem calibrationCoefficient_constant (U : UnstableDescendantConventions M I) :
    U.calibrationCoefficient 0 0 = LinearMap.id := by
  rw [calibrationCoefficient, if_pos rfl]

/-- There is no constant-in-loop-degree term at positive curve class. -/
theorem calibrationCoefficient_zero_power (U : UnstableDescendantConventions M I)
    (beta : B) (hbeta : beta ≠ 0) : U.calibrationCoefficient 0 beta = 0 := by
  rw [calibrationCoefficient, if_neg hbeta]

/-- The descendant exponent is one less than the inverse-loop power. -/
theorem calibrationCoefficient_pairing (U : UnstableDescendantConventions M I)
    (m : ℕ) (beta : B) (x y : V) :
    Omega.pairing.form x (U.calibrationCoefficient (m + 1) beta y) =
      U.invariant 0 (Fin 2) beta ![0, m] ![x, y] := by
  rw [calibrationCoefficient, Omega.pairing.raiseTwoPoint_pairing, U.invariantMap_apply]

/-- Relabelling the two primary insertions makes the first coefficient self-adjoint.
This verifies the first-order symmetry condition without asserting full symplecticity. -/
theorem calibrationCoefficient_one_selfAdjoint (U : UnstableDescendantConventions M I)
    (beta : B) (x y : V) :
    Omega.pairing.form x (U.calibrationCoefficient 1 beta y) =
      Omega.pairing.form (U.calibrationCoefficient 1 beta x) y := by
  have hk : (fun t ↦ (![0,0] : Fin 2 → ℕ) (SymmetricPerfectPairing.swapFinTwo.symm t)) =
      ![0,0] := by
    funext i
    fin_cases i <;> rfl
  have he := U.invariant_relabel 0 (Fin 2) (Fin 2)
    SymmetricPerfectPairing.swapFinTwo beta ![0,0]
  rw [hk] at he
  have hv := congrArg (fun f ↦ f ![y,x]) he
  rw [MultilinearMap.domDomCongr_apply] at hv
  have ha : (fun i ↦ (![y,x] : Fin 2 → V) (SymmetricPerfectPairing.swapFinTwo i)) =
      ![x,y] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, U.invariantMap_apply, U.invariantMap_apply] at hv
  rw [U.calibrationCoefficient_pairing, Omega.pairing.isSymm.eq _ y,
    U.calibrationCoefficient_pairing]
  exact hv

/-- Positive inverse-loop powers have no degree-zero two-point contribution. -/
theorem calibrationCoefficient_zero_class (U : UnstableDescendantConventions M I)
    (m : ℕ) : U.calibrationCoefficient (m + 1) 0 = 0 := by
  have hmap : U.invariantMap 0 (Fin 2) 0 ![0, m] = 0 := by
    ext a
    rw [U.invariantMap_apply,
      U.invariant_zero_of_unstable 0 (Fin 2) (by norm_num [StableArity])]
    rfl
  rw [calibrationCoefficient, hmap, Omega.pairing.raiseTwoPoint_zero]

/-- The existing calibration carrier, now constructed from numerical GW data. -/
noncomputable def twoPointCalibration (U : UnstableDescendantConventions M I) :
    TwoPointCalibration D Omega.pairing where
  coefficient := U.calibrationCoefficient
  coefficient_zero := U.calibrationCoefficient_constant

/-- Sewing an actual two-point tail is application of its calibration coefficient. -/
theorem calibrationCoefficient_contract (U : UnstableDescendantConventions M I)
    (m : ℕ) (beta : B) (ell : Module.Dual R V) (y : V) :
    TensorProduct.lift
        (((LinearMap.mul R R).comp ell).compl₂
          ((SymmetricPerfectPairing.finTwoToBilin
            (U.invariantMap 0 (Fin 2) beta ![0, m])).flip y))
        Omega.pairing.copairing = ell (U.calibrationCoefficient (m + 1) beta y) :=
  Omega.pairing.raiseTwoPoint_contract _ ell y

/-- The two-point virtual dimension filters every paired coefficient, with signed degree. -/
theorem calibrationCoefficient_pairing_eq_zero_of_degree_ne
    (U : UnstableDescendantConventions M I) (m : ℕ) (beta : B)
    (x y : V) (dx dy : ℕ)
    (hx : x ∈ Omega.graded.degree dx) (hy : y ∈ Omega.graded.degree dy)
    (hne : (dx : ℤ) + (dy : ℤ) + (m : ℤ) ≠
      (Omega.graded.dimension : ℤ) - 1 + Omega.c1Degree beta) :
    Omega.pairing.form x (U.calibrationCoefficient (m + 1) beta y) = 0 := by
  rw [U.calibrationCoefficient_pairing]
  apply U.invariant_eq_zero_of_degree_ne 0 (Fin 2) beta ![0, m] ![dx, dy] ![x, y]
  · intro i
    fin_cases i
    · exact hx
    · exact hy
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_add, Nat.cast_add, Fintype.card_fin, GWVirtualDimension,
      Nat.cast_ofNat, Nat.cast_zero, sub_zero, mul_one]
    omega

end UnstableDescendantConventions

namespace TwoPointCalibration

/-- Paired geometric values and the full constant-in-loop-degree normalization.
The first conjunct rules out spurious `z^0 q^beta` terms at positive class. -/
def IsFromDescendants (S : TwoPointCalibration D Omega.pairing)
    (U : UnstableDescendantConventions M I) : Prop :=
  (∀ beta, beta ≠ 0 → S.coefficient 0 beta = 0) ∧
  ∀ m beta x y, Omega.pairing.form x (S.coefficient (m + 1) beta y) =
    U.invariant 0 (Fin 2) beta ![0, m] ![x, y]

/-- The coefficient construction satisfies precisely its paired geometric specification. -/
theorem twoPointCalibration_isFromDescendants (U : UnstableDescendantConventions M I) :
    U.twoPointCalibration.IsFromDescendants U :=
  ⟨U.calibrationCoefficient_zero_power, U.calibrationCoefficient_pairing⟩

/-- No independent choice of operators remains after identifying all paired two-point values. -/
theorem eq_of_isFromDescendants (S : TwoPointCalibration D Omega.pairing)
    (U : UnstableDescendantConventions M I) (h : S.IsFromDescendants U) :
    S = U.twoPointCalibration := by
  have he : S.coefficient = U.twoPointCalibration.coefficient := by
    funext power beta
    cases power with
    | zero =>
        by_cases hb : beta = 0
        · subst beta
          exact S.coefficient_zero.trans U.calibrationCoefficient_constant.symm
        · exact (h.1 beta hb).trans (U.calibrationCoefficient_zero_power beta hb).symm
    | succ m =>
        apply Omega.pairing.raiseTwoPoint_unique
        intro x y
        rw [U.invariantMap_apply]
        exact h.2 m beta x y
  rcases S with ⟨coefficient, coefficient_zero⟩
  change coefficient = U.calibrationCoefficient at he
  subst coefficient
  rfl

end TwoPointCalibration

namespace StabilizationBoundaryComparison
variable {P : PsiClasses C}

/-- Explicit identification of the stored tail operators with actual two-point descendants. -/
def TwoPointCompatible (X : StabilizationBoundaryComparison P M)
    (U : UnstableDescendantConventions M I) : Prop :=
  X.calibration.IsFromDescendants U

/-- Paired geometric identification determines the entire stored calibration. -/
theorem calibration_eq_twoPointCalibration (X : StabilizationBoundaryComparison P M)
    (U : UnstableDescendantConventions M I) (h : X.TwoPointCompatible U) :
    X.calibration = U.twoPointCalibration :=
  X.calibration.eq_of_isFromDescendants U h

/-- Every tail coefficient is the one obtained by raising the actual two-point node index. -/
theorem tailCoefficient_eq (X : StabilizationBoundaryComparison P M)
    (U : UnstableDescendantConventions M I) (h : X.TwoPointCompatible U)
    (power : ℕ) (beta : B) :
    X.twoPointTailCoefficient power beta = U.calibrationCoefficient power beta :=
  congrArg (fun S ↦ S.coefficient power beta) (X.calibration_eq_twoPointCalibration U h)

/-- The existing rational-tail sum now uses actual numerical two-point operators.
Its main boundary maps and geometric residual identity are still explicit inputs. -/
theorem correction_eq_descendant_tails (X : StabilizationBoundaryComparison P M)
    (U : UnstableDescendantConventions M I) (h : X.TwoPointCompatible U)
    (g : ℕ) (S : Type) [Fintype S] (hs : StableArity g S) (beta : B) (k : S → ℕ) :
    X.toDescendantAncestorComparison.boundaryCorrection g S hs beta k =
      ∑ s, ∑ split ∈ D.positiveTailSplittings beta,
        X.tailWeight g S hs beta k s split • X.mainBoundary g S hs beta k s split
          (U.calibrationCoefficient (k s) split.2) := by
  rw [X.correction_eq_positive_tail_sum]
  simp only [X.tailCoefficient_eq U h]

end StabilizationBoundaryComparison
end AxiomaticGW
