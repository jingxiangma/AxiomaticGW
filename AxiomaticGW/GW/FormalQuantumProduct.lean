/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.Potentials
public import AxiomaticGW.GW.QuantumProduct

/-!
# Formal big quantum product

The genus-zero primary invariants define a state-valued formal series with
three distinguished insertions. Its zero-background coefficient is the small
quantum product. Relabelling proves commutativity coefficientwise.
Associativity at nonzero background requires the higher-point genus-zero
boundary relation and is deliberately not asserted here.
-/

@[expose] public section

namespace AxiomaticGW

open Module

universe u

/-- A formal power series whose coefficients are Novikov-valued states. -/
abbrev FormalStateSeries {B : Type*} [AddCancelCommMonoid B]
    (D : EffectiveCurveMonoid B) (Vars V : Type*) :=
  MvPowerSeries Vars (NovikovSeries D V)

namespace CurveClassGW

variable {R V B : Type u} {ι : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R}

/-- Three distinguished genus-zero insertions are stable at every background
profile. -/
theorem formalBigProduct_stable (n : ι →₀ ℕ) :
    StableArity 0 (Fin 3 ⊕ InsertionLabel n) := by
  simp [StableArity]

/-- The three-point series at a primary background profile. The reciprocal
multiplicity factorial accounts only for the undistinguished background
insertions. -/
noncomputable def primaryThreePointSeriesCoefficient
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) :
    MultilinearMap R (fun _ : Fin 3 ↦ V) R := by
  let full := (I.integrate 0 (Fin 3 ⊕ InsertionLabel n)
    (formalBigProduct_stable n)).compMultilinearMap
      (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
        (formalBigProduct_stable n) beta)
  let evaluateBackground :
      MultilinearMap R (fun _ : InsertionLabel n ↦ V) R →ₗ[R] R :=
    { toFun := fun f ↦ f (InsertionLabel.primaryState b)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact profileWeight R n •
    evaluateBackground.compMultilinearMap full.currySum

@[simp]
theorem primaryThreePointSeriesCoefficient_apply
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) (a : Fin 3 → V) :
    Omega.primaryThreePointSeriesCoefficient I b n beta a =
      profileWeight R n *
        I.integrate 0 (Fin 3 ⊕ InsertionLabel n)
          (formalBigProduct_stable n)
          (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
            (formalBigProduct_stable n) beta
            (Sum.elim a (InsertionLabel.primaryState b))) := rfl

/-- The primary three-point series is invariant under permutations of its
three distinguished insertions. Background insertions remain fixed. -/
theorem primaryThreePointSeriesCoefficient_relabel
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
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
      (Fin 3 ⊕ InsertionLabel n) (formalBigProduct_stable n)
      (formalBigProduct_stable n) e beta)
  change C.rename 0 (Fin 3 ⊕ InsertionLabel n)
      (Fin 3 ⊕ InsertionLabel n) (formalBigProduct_stable n)
      (formalBigProduct_stable n) e
        (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
          (formalBigProduct_stable n) beta (fullInput ∘ e)) =
    Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
      (formalBigProduct_stable n) beta fullInput at hrel
  simp only [MultilinearMap.domDomCongr_apply,
    Omega.primaryThreePointSeriesCoefficient_apply]
  rw [hinputs]
  congr 1
  calc
    I.integrate 0 (Fin 3 ⊕ InsertionLabel n) (formalBigProduct_stable n)
        (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
          (formalBigProduct_stable n) beta (fullInput ∘ e)) =
      I.integrate 0 (Fin 3 ⊕ InsertionLabel n) (formalBigProduct_stable n)
        (C.rename 0 (Fin 3 ⊕ InsertionLabel n)
          (Fin 3 ⊕ InsertionLabel n) (formalBigProduct_stable n)
          (formalBigProduct_stable n) e
          (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
            (formalBigProduct_stable n) beta (fullInput ∘ e))) :=
      (I.integrate_rename 0 (Fin 3 ⊕ InsertionLabel n)
        (Fin 3 ⊕ InsertionLabel n) (formalBigProduct_stable n)
        (formalBigProduct_stable n) e _).symm
    _ = I.integrate 0 (Fin 3 ⊕ InsertionLabel n)
        (formalBigProduct_stable n)
        (Omega.omega 0 (Fin 3 ⊕ InsertionLabel n)
          (formalBigProduct_stable n) beta fullInput) := by rw [hrel]

/-- Symmetry of the first two distinguished inputs of the primary
three-point series. -/
theorem primaryThreePointSeriesCoefficient_swap_first
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
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
noncomputable def formalBigProductCoefficient
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) :
    V →ₗ[R] V →ₗ[R] V :=
  (LinearMap.compRight R
      (LinearMap.compRight R Omega.pairing.toDual.symm.toLinearMap)).comp
    ((LinearMap.compRight R
      (SymmetricPerfectPairing.finTwoToBilin (R := R) (V := V))).comp
        (multilinearCurryLeftEquiv R (fun _ : Fin 3 ↦ V) R).toLinearMap) <|
          Omega.primaryThreePointSeriesCoefficient I b n beta

/-- The formal big quantum product of two ordinary states. It is a power
series in primary variables and a Novikov series in curve classes. -/
noncomputable def formalBigProduct
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (x y : V) : FormalStateSeries D ι V :=
  fun n beta ↦ Omega.formalBigProductCoefficient I b n beta x y

@[simp]
theorem formalBigProduct_apply
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (x y : V) (n : ι →₀ ℕ) (beta : B) :
    Omega.formalBigProduct I b x y n beta =
      Omega.formalBigProductCoefficient I b n beta x y := rfl

/-- The formal product is characterized by the primary three-point series. -/
theorem pairing_formalBigProductCoefficient
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) (x y z : V) :
    Omega.pairing.form
        (Omega.formalBigProductCoefficient I b n beta x y) z =
      Omega.primaryThreePointSeriesCoefficient I b n beta
        (Fin.cons x (Fin.cons y fun _ ↦ z)) := by
  rw [← Omega.pairing.toDual_apply]
  simp [formalBigProductCoefficient,
    SymmetricPerfectPairing.finTwoToBilin_apply]

/-- Every coefficient of the formal big quantum product is commutative. -/
theorem formalBigProductCoefficient_comm
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) (x y : V) :
    Omega.formalBigProductCoefficient I b n beta x y =
      Omega.formalBigProductCoefficient I b n beta y x := by
  apply Omega.pairing.toDual.injective
  ext z
  simp only [Omega.pairing.toDual_apply,
    Omega.pairing_formalBigProductCoefficient]
  exact Omega.primaryThreePointSeriesCoefficient_swap_first
    I b n beta x y z

/-- The completed formal big quantum product is commutative. -/
theorem formalBigProduct_comm
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (x y : V) :
    Omega.formalBigProduct I b x y = Omega.formalBigProduct I b y x := by
  funext n beta
  exact Omega.formalBigProductCoefficient_comm I b n beta x y

private def zeroBackgroundEquiv :
    Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ) ≃ Fin 3 where
  toFun
    | .inl i => i
    | .inr s => Fin.elim0 (by simpa using s.2)
  invFun := Sum.inl
  left_inv x := by
    rcases x with i | s
    · rfl
    · exact Fin.elim0 (by simpa using s.2)
  right_inv _ := rfl

/-- At zero background, the primary three-point series is the fixed-beta
three-point invariant. The hypothesis is exactly the compatibility between
integration over `Mbar(0,3)` and its canonical scalar identification. -/
theorem primaryThreePointSeriesCoefficient_zero
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
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
    · exact Fin.elim0 (by simpa using s.2)
  have hrel := congrArg (fun f ↦ f a)
    (Omega.relabel 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ)) (Fin 3)
      (formalBigProduct_stable 0) StableArity.zero_fin_three e beta)
  change C.rename 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ)) (Fin 3)
      (formalBigProduct_stable 0) StableArity.zero_fin_three e
        (Omega.omega 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ))
          (formalBigProduct_stable 0) beta (a ∘ e)) =
    Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta a at hrel
  rw [Omega.primaryThreePointSeriesCoefficient_apply]
  simp only [threePoint, LinearMap.compMultilinearMap_apply]
  rw [show profileWeight R (0 : ι →₀ ℕ) = 1 by
    simp [profileWeight, profileFactorial]]
  rw [one_mul, hinputs]
  calc
    I.integrate 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ))
        (formalBigProduct_stable 0)
        (Omega.omega 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ))
          (formalBigProduct_stable 0) beta (a ∘ e)) =
      I.integrate 0 (Fin 3) StableArity.zero_fin_three
        (C.rename 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ)) (Fin 3)
          (formalBigProduct_stable 0) StableArity.zero_fin_three e
          (Omega.omega 0 (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ))
            (formalBigProduct_stable 0) beta (a ∘ e))) :=
        (I.integrate_rename 0
          (Fin 3 ⊕ InsertionLabel (0 : ι →₀ ℕ)) (Fin 3)
          (formalBigProduct_stable 0) StableArity.zero_fin_three e _).symm
    _ = I.integrate 0 (Fin 3) StableArity.zero_fin_three
        (Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta a) := by
      rw [hrel]
    _ = G.mbarZeroThree
        (Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta a) := by
      rw [hI]
      rfl

/-- The zero-background coefficient of the formal big product is the small
quantum product coefficient. -/
theorem formalBigProductCoefficient_zero
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (G : GenusZeroGeometry C) (b : Basis ι R V)
    (hI : I.integrate 0 (Fin 3) StableArity.zero_fin_three =
      G.mbarZeroThree.toLinearMap) (beta : B) :
    Omega.formalBigProductCoefficient I b 0 beta =
      Omega.smallProductCoefficient G beta := by
  simp only [formalBigProductCoefficient, smallProductCoefficient,
    Omega.primaryThreePointSeriesCoefficient_zero I G b hI beta]

/-- The formal big product specializes coefficientwise to the small product
at zero primary background. -/
theorem formalBigProduct_zero
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (G : GenusZeroGeometry C) (b : Basis ι R V)
    (hI : I.integrate 0 (Fin 3) StableArity.zero_fin_three =
      G.mbarZeroThree.toLinearMap) (x y : V) (beta : B) :
    Omega.formalBigProduct I b x y 0 beta =
      Omega.smallProductCoefficient G beta x y := by
  rw [Omega.formalBigProduct_apply,
    Omega.formalBigProductCoefficient_zero I G b hI]

end CurveClassGW

end AxiomaticGW
