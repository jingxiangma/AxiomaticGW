/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.Potentials
public import AxiomaticGW.GW.SmallQuantumProduct
public import Mathlib.Data.Finsupp.Antidiagonal

/-!
# Big quantum product and genus-zero WDVV

The genus-zero primary invariants define a state-valued formal series with
three distinguished insertions. Its zero-background coefficient is the small
quantum product, and relabelling proves commutativity coefficientwise.
Associativity at nonzero background follows from the separately stated
genus-zero WDVV relation. The same coefficients define the primary potential.
-/

@[expose] public section

namespace AxiomaticGW

open Module

universe u

/-- A formal power series whose coefficients are Novikov-valued states. -/
abbrev FormalStateSeries {B : Type*} [AddCancelCommMonoid B]
    (D : EffectiveCurveMonoid B) (Vars V : Type*) :=
  MvPowerSeries Vars (NovikovSeries D V)

namespace GromovWittenTheory

variable {R V B : Type u} {ι : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R}

/-- Three distinguished genus-zero insertions are stable at every background
profile. -/
theorem bigQuantumProduct_stable (n : ι →₀ ℕ) :
    StableArity 0 (Fin 3 ⊕ InsertionLabel n) := by
  simp only [StableArity, mul_zero, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_sigma, Finset.univ_eq_attach, zero_add,
    le_add_iff_nonneg_right, zero_le]

/-- The three-point series at a primary background profile. The reciprocal
multiplicity factorial accounts only for the undistinguished background
insertions. -/
noncomputable def primaryThreePointSeriesCoefficient
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) :
    MultilinearMap R (fun _ : Fin 3 ↦ V) R := by
  let full := (I.integrate 0 (Fin 3 ⊕ InsertionLabel n)
    (bigQuantumProduct_stable n)).compMultilinearMap
      (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
        (bigQuantumProduct_stable n) beta)
  let evaluateBackground :
      MultilinearMap R (fun _ : InsertionLabel n ↦ V) R →ₗ[R] R :=
    { toFun := fun f ↦ f (InsertionLabel.primaryState b)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact profileWeight R n •
    evaluateBackground.compMultilinearMap full.currySum

@[simp]
theorem primaryThreePointSeriesCoefficient_apply
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) (a : Fin 3 → V) :
    Omega.primaryThreePointSeriesCoefficient I b n beta a =
      profileWeight R n *
        I.integrate 0 (Fin 3 ⊕ InsertionLabel n)
          (bigQuantumProduct_stable n)
          (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
            (bigQuantumProduct_stable n) beta
            (Sum.elim a (InsertionLabel.primaryState b))) := rfl

/-- The primary three-point series is invariant under permutations of its
three distinguished insertions. Background insertions remain fixed. -/
theorem primaryThreePointSeriesCoefficient_relabel
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B)
    (perm : Equiv.Perm (Fin 3)) :
    (Omega.primaryThreePointSeriesCoefficient I b n beta).domDomCongr perm =
      Omega.primaryThreePointSeriesCoefficient I b n beta := by
  apply MultilinearMap.ext
  intro a
  let e : Fin 3 ⊕ InsertionLabel n ≃ Fin 3 ⊕ InsertionLabel n :=
    Equiv.sumCongr perm (Equiv.refl (InsertionLabel n))
  let fullInput : Fin 3 ⊕ InsertionLabel n → V :=
    Sum.elim a (InsertionLabel.primaryState b)
  have hinputs : Sum.elim (fun i ↦ a (perm i))
      (InsertionLabel.primaryState b) = fullInput ∘ e := by
    funext s
    rcases s with s | s <;> rfl
  have hrel := congrArg (fun f ↦ f fullInput)
    (Omega.relabel 0 (Fin 3 ⊕ InsertionLabel n)
      (Fin 3 ⊕ InsertionLabel n) (bigQuantumProduct_stable n)
      (bigQuantumProduct_stable n) e beta)
  change C.rename 0 (Fin 3 ⊕ InsertionLabel n)
      (Fin 3 ⊕ InsertionLabel n) (bigQuantumProduct_stable n)
      (bigQuantumProduct_stable n) e
        (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
          (bigQuantumProduct_stable n) beta (fullInput ∘ e)) =
    Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
      (bigQuantumProduct_stable n) beta fullInput at hrel
  simp only [MultilinearMap.domDomCongr_apply,
    Omega.primaryThreePointSeriesCoefficient_apply]
  rw [hinputs]
  congr 1
  calc
    I.integrate 0 (Fin 3 ⊕ InsertionLabel n) (bigQuantumProduct_stable n)
        (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
          (bigQuantumProduct_stable n) beta (fullInput ∘ e)) =
      I.integrate 0 (Fin 3 ⊕ InsertionLabel n) (bigQuantumProduct_stable n)
        (C.rename 0 (Fin 3 ⊕ InsertionLabel n)
          (Fin 3 ⊕ InsertionLabel n) (bigQuantumProduct_stable n)
          (bigQuantumProduct_stable n) e
          (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
            (bigQuantumProduct_stable n) beta (fullInput ∘ e))) :=
      (I.integrate_rename 0 (Fin 3 ⊕ InsertionLabel n)
        (Fin 3 ⊕ InsertionLabel n) (bigQuantumProduct_stable n)
        (bigQuantumProduct_stable n) e _).symm
    _ = I.integrate 0 (Fin 3 ⊕ InsertionLabel n)
        (bigQuantumProduct_stable n)
        (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
          (bigQuantumProduct_stable n) beta fullInput) := by rw [hrel]

/-- Symmetry of the first two distinguished inputs of the primary
three-point series. -/
theorem primaryThreePointSeriesCoefficient_swap_first
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) (x y z : V) :
    Omega.primaryThreePointSeriesCoefficient I b n beta
        (Fin.cons x (Fin.cons y fun _ ↦ z)) =
      Omega.primaryThreePointSeriesCoefficient I b n beta
        (Fin.cons y (Fin.cons x fun _ ↦ z)) := by
  let a : Fin 3 → V := Fin.cons x (Fin.cons y fun _ ↦ z)
  have h := congrArg (fun f ↦ f a)
    (Omega.primaryThreePointSeriesCoefficient_relabel I b n beta
      (Equiv.swap 0 1))
  change Omega.primaryThreePointSeriesCoefficient I b n beta
      (a ∘ Equiv.swap 0 1) =
    Omega.primaryThreePointSeriesCoefficient I b n beta a at h
  rw [← h]
  congr 1
  funext j
  fin_cases j <;> rfl

/-- Raise the third distinguished insertion using the target metric. -/
noncomputable def bigQuantumProductCoefficient
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) :
    V →ₗ[R] V →ₗ[R] V :=
  (LinearMap.compRight R
      (LinearMap.compRight R Omega.pairing.toDual.symm.toLinearMap)).comp
    ((LinearMap.compRight R
      (SymmetricPerfectPairing.finTwoToBilin (R := R) (V := V))).comp
        (multilinearCurryLeftEquiv R (fun _ : Fin 3 ↦ V) R).toLinearMap) <|
          Omega.primaryThreePointSeriesCoefficient I b n beta

/-- The big quantum product of two ordinary states. It is a power
series in primary variables and a Novikov series in curve classes. -/
noncomputable def bigQuantumProduct
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (x y : V) : FormalStateSeries D ι V :=
  fun n beta ↦ Omega.bigQuantumProductCoefficient I b n beta x y

@[simp]
theorem bigQuantumProduct_apply
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (x y : V) (n : ι →₀ ℕ) (beta : B) :
    Omega.bigQuantumProduct I b x y n beta =
      Omega.bigQuantumProductCoefficient I b n beta x y := rfl

/-- The big quantum product is characterized by the primary three-point series. -/
theorem pairing_bigQuantumProductCoefficient
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) (x y z : V) :
    Omega.pairing.form
        (Omega.bigQuantumProductCoefficient I b n beta x y) z =
      Omega.primaryThreePointSeriesCoefficient I b n beta
        (Fin.cons x (Fin.cons y fun _ ↦ z)) := by
  rw [← Omega.pairing.toDual_apply]
  simp only [bigQuantumProductCoefficient, Nat.succ_eq_add_one,
    Nat.reduceAdd, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, multilinearCurryLeftEquiv_apply,
    LinearMap.compRight_apply, LinearEquiv.apply_symm_apply,
    SymmetricPerfectPairing.finTwoToBilin_apply,
    MultilinearMap.curryLeft_apply, primaryThreePointSeriesCoefficient_apply]

/-- Every coefficient of the big quantum product is commutative. -/
theorem bigQuantumProductCoefficient_comm
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) (x y : V) :
    Omega.bigQuantumProductCoefficient I b n beta x y =
      Omega.bigQuantumProductCoefficient I b n beta y x := by
  apply Omega.pairing.toDual.injective
  ext z
  simp only [Omega.pairing.toDual_apply,
    Omega.pairing_bigQuantumProductCoefficient]
  exact Omega.primaryThreePointSeriesCoefficient_swap_first
    I b n beta x y z

/-- The big quantum product is commutative. -/
theorem bigQuantumProduct_comm
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (x y : V) :
    Omega.bigQuantumProduct I b x y = Omega.bigQuantumProduct I b y x := by
  funext n beta
  exact Omega.bigQuantumProductCoefficient_comm I b n beta x y

private def zeroBackgroundEquiv :
    Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ) ≃ Fin 3 where
  toFun
    | .inl i => i
    | .inr s => Fin.elim0 (by
        simpa only [Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply]
          using s.2)
  invFun := Sum.inl
  left_inv x := by
    rcases x with i | s
    · rfl
    · exact Fin.elim0 (by
        simpa only [Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply]
          using s.2)
  right_inv _ := rfl

/-- At zero background, the primary three-point series is the fixed-beta
three-point invariant. The hypothesis is exactly the compatibility between
integration over `Mbar(0,3)` and its canonical scalar identification. -/
theorem primaryThreePointSeriesCoefficient_zero
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (G : GenusZeroGeometry C) (b : Basis ι R V)
    (hI : I.integrate 0 (Fin 3) StableArity.zero_fin_three =
      G.mbarZeroThree.toLinearMap) (beta : B) :
    Omega.primaryThreePointSeriesCoefficient I b 0 beta =
      Omega.threePoint G beta := by
  apply MultilinearMap.ext
  intro a
  let e : Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ) ≃ Fin 3 :=
    zeroBackgroundEquiv
  have hinputs :
      Sum.elim a (InsertionLabel.primaryState b) = a ∘ e := by
    funext s
    rcases s with i | s
    · rfl
    · exact Fin.elim0 (by
        simpa only [Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply]
          using s.2)
  have hrel := congrArg (fun f ↦ f a)
    (Omega.relabel 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ)) (Fin 3)
      (bigQuantumProduct_stable 0) StableArity.zero_fin_three e beta)
  change C.rename 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ)) (Fin 3)
      (bigQuantumProduct_stable 0) StableArity.zero_fin_three e
        (Omega.omega 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ))
          (bigQuantumProduct_stable 0) beta (a ∘ e)) =
    Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta a at hrel
  rw [Omega.primaryThreePointSeriesCoefficient_apply]
  simp only [threePoint, LinearMap.compMultilinearMap_apply]
  rw [show profileWeight R (0 : ι →₀ ℕ) = 1 by
    simp only [profileWeight, profileFactorial, Finsupp.prod_zero_index,
      Nat.cast_one, inv_one, map_one]]
  rw [one_mul, hinputs]
  calc
    I.integrate 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ))
        (bigQuantumProduct_stable 0)
        (Omega.omega 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ))
          (bigQuantumProduct_stable 0) beta (a ∘ e)) =
      I.integrate 0 (Fin 3) StableArity.zero_fin_three
        (C.rename 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ)) (Fin 3)
          (bigQuantumProduct_stable 0) StableArity.zero_fin_three e
          (Omega.omega 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ))
            (bigQuantumProduct_stable 0) beta (a ∘ e))) :=
        (I.integrate_rename 0
          (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ)) (Fin 3)
          (bigQuantumProduct_stable 0) StableArity.zero_fin_three e _).symm
    _ = I.integrate 0 (Fin 3) StableArity.zero_fin_three
        (Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta a) := by
      rw [hrel]
    _ = G.mbarZeroThree
        (Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta a) := by
      rw [hI]
      rfl

/-- The zero-background coefficient of the big quantum product is the small
quantum product coefficient. -/
theorem bigQuantumProductCoefficient_zero
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (G : GenusZeroGeometry C) (b : Basis ι R V)
    (hI : I.integrate 0 (Fin 3) StableArity.zero_fin_three =
      G.mbarZeroThree.toLinearMap) (beta : B) :
    Omega.bigQuantumProductCoefficient I b 0 beta =
      Omega.smallQuantumProductCoefficient G beta := by
  simp only [bigQuantumProductCoefficient, smallQuantumProductCoefficient,
    Omega.primaryThreePointSeriesCoefficient_zero I G b hI beta]

/-- The big quantum product specializes coefficientwise to the small quantum
product at zero primary background. -/
theorem bigQuantumProduct_zero
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (G : GenusZeroGeometry C) (b : Basis ι R V)
    (hI : I.integrate 0 (Fin 3) StableArity.zero_fin_three =
      G.mbarZeroThree.toLinearMap) (x y : V) (beta : B) :
    Omega.bigQuantumProduct I b x y 0 beta =
      Omega.smallQuantumProductCoefficient G beta x y := by
  rw [Omega.bigQuantumProduct_apply,
    Omega.bigQuantumProductCoefficient_zero I G b hI]

/-- Coefficient of `(x star y) star z` at one primary profile and curve
class. Both the background profile and the effective class are split. -/
noncomputable def bigQuantumProductAssocLeftCoefficient
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) (x y z : V) : V := by
  classical
  exact ∑ profileSplit ∈ Finset.HasAntidiagonal.antidiagonal n,
    ∑ curveSplit ∈ D.splittings beta,
      Omega.bigQuantumProductCoefficient I b profileSplit.2 curveSplit.2
        (Omega.bigQuantumProductCoefficient I b profileSplit.1 curveSplit.1 x y) z

/-- Coefficient of `x star (y star z)` at one primary profile and curve
class. -/
noncomputable def bigQuantumProductAssocRightCoefficient
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) (x y z : V) : V := by
  classical
  exact ∑ profileSplit ∈ Finset.HasAntidiagonal.antidiagonal n,
    ∑ curveSplit ∈ D.splittings beta,
      Omega.bigQuantumProductCoefficient I b profileSplit.1 curveSplit.1 x
        (Omega.bigQuantumProductCoefficient I b profileSplit.2 curveSplit.2 y z)

/-- The scalar genus-zero WDVV relation at an arbitrary primary background.
It is independent geometric input; state-valued associativity is derived from
it using nondegeneracy of the pairing. -/
structure GenusZeroWDVV
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) where
  /-- Equality of the two four-point boundary channels for every background
  profile and effective curve class. -/
  wdvv : ∀ (n : ι →₀ ℕ) (beta : B) (x y z w : V),
    Omega.pairing.form
        (Omega.bigQuantumProductAssocLeftCoefficient I b n beta x y z) w =
      Omega.pairing.form
        (Omega.bigQuantumProductAssocRightCoefficient I b n beta x y z) w

/-- Genus-zero WDVV implies coefficientwise associativity of the big quantum
product. -/
theorem bigQuantumProductCoefficient_assoc
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (H : GenusZeroWDVV Omega I b)
    (n : ι →₀ ℕ) (beta : B) (x y z : V) :
    Omega.bigQuantumProductAssocLeftCoefficient I b n beta x y z =
      Omega.bigQuantumProductAssocRightCoefficient I b n beta x y z := by
  apply Omega.pairing.toDual.injective
  ext w
  simpa only [Omega.pairing.toDual_apply] using H.wdvv n beta x y z w

/-- Associativity of the big quantum product, stated coefficientwise in the
primary variables and Novikov classes. -/
theorem bigQuantumProduct_associative
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (H : GenusZeroWDVV Omega I b)
    (x y z : V) :
    (fun n beta ↦
      Omega.bigQuantumProductAssocLeftCoefficient I b n beta x y z) =
      fun n beta ↦
        Omega.bigQuantumProductAssocRightCoefficient I b n beta x y z := by
  funext n beta
  exact Omega.bigQuantumProductCoefficient_assoc I b H n beta x y z

/-- Genus-zero primary potential. Its coefficient is the integrated primary
invariant divided by the multiplicity factorial; unstable arities are zero. -/
noncomputable def primaryPotential
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) : FormalPotential D ι R := by
  classical
  intro n beta
  exact if h : StableArity 0 (InsertionLabel n) then
    profileWeight R n *
      I.integrate 0 (InsertionLabel n) h
        (Omega.omega 0 (InsertionLabel n) h beta
          (InsertionLabel.primaryState b))
  else 0

@[simp]
theorem primaryPotential_coeff_of_stable
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B)
    (h : StableArity 0 (InsertionLabel n)) :
    Omega.primaryPotential I b n beta =
      profileWeight R n *
        I.integrate 0 (InsertionLabel n) h
          (Omega.omega 0 (InsertionLabel n) h beta
            (InsertionLabel.primaryState b)) := by
  simp only [primaryPotential, h, ↓reduceDIte]

@[simp]
theorem primaryPotential_coeff_of_unstable
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B)
    (h : ¬StableArity 0 (InsertionLabel n)) :
    Omega.primaryPotential I b n beta = 0 := by
  simp only [primaryPotential, h, ↓reduceDIte]

end GromovWittenTheory

end AxiomaticGW
