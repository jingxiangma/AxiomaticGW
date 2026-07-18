/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.GenusZero
public import AxiomaticGW.TFT.Correlator
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Frobenius algebra extracted from a CohFT

The three-point genus-zero class is scalar because `Mbar(0,3)` is a point.
Raising its third input with the perfect metric produces the CohFT product.
-/

@[expose] public section

namespace AxiomaticGW

private def optionFinTwoEquivFinThree : Option (Fin 2) ≃ Fin 3 :=
  (finSuccEquiv 2).symm

namespace GenusZeroCohFT

variable {R V : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  {C : StableCurveCohomology R}

/-- The scalar three-point correlator supplied by the point geometry of
`Mbar(0,3)`. -/
noncomputable def threePoint (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) :
    MultilinearMap R (fun _ : Fin 3 ↦ V) R :=
  G.mbarZeroThree.toLinearMap.compMultilinearMap
    (T.omega (Fin 3) StableArity.zero_fin_three)

/-- The scalar three-point correlator, curried into three linear inputs. -/
noncomputable def threePointFunction (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) : V →ₗ[R] V →ₗ[R] V →ₗ[R] R :=
  (LinearMap.compRight R
    (SymmetricPerfectPairing.finTwoToBilin (R := R) (V := V))).comp
    (multilinearCurryLeftEquiv R (fun _ : Fin 3 ↦ V) R).toLinearMap <|
      T.threePoint G

/-- Evaluation of the curried scalar three-point correlator. -/
@[simp]
theorem threePointFunction_apply (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x y z : V) :
    T.threePointFunction G x y z =
      T.threePoint G (Fin.cons x (Fin.cons y fun _ ↦ z)) := by
  simp only [threePointFunction, Nat.succ_eq_add_one, Nat.reduceAdd,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    multilinearCurryLeftEquiv_apply, LinearMap.compRight_apply,
    SymmetricPerfectPairing.finTwoToBilin_apply,
    MultilinearMap.curryLeft_apply]

/-- The product obtained by raising the last index of the three-point
correlator with the inverse metric. -/
noncomputable def product (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) : V →ₗ[R] V →ₗ[R] V :=
  (LinearMap.compRight R
      (LinearMap.compRight R T.pairing.toDual.symm.toLinearMap)).comp
    ((LinearMap.compRight R
      (SymmetricPerfectPairing.finTwoToBilin (R := R) (V := V))).comp
      (multilinearCurryLeftEquiv R (fun _ : Fin 3 ↦ V) R).toLinearMap) <|
        T.threePoint G

/-- The extracted product is characterized by the original three-point
correlator. -/
theorem pairing_product (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x y z : V) :
    T.pairing.form (T.product G x y) z = T.threePointFunction G x y z := by
  rw [← T.pairing.toDual_apply]
  simp only [product, Nat.succ_eq_add_one, Nat.reduceAdd,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    multilinearCurryLeftEquiv_apply, LinearMap.compRight_apply,
    LinearEquiv.apply_symm_apply, SymmetricPerfectPairing.finTwoToBilin_apply,
    MultilinearMap.curryLeft_apply, threePointFunction]

/-- The point identification of `Mbar(0,3)` is insensitive to relabelling. -/
theorem _root_.AxiomaticGW.GenusZeroGeometry.mbarZeroThree_rename
    (G : GenusZeroGeometry C) (e : Equiv.Perm (Fin 3)) (x : C.H 0 (Fin 3)) :
    G.mbarZeroThree
        (C.rename 0 (Fin 3) (Fin 3) StableArity.zero_fin_three
          StableArity.zero_fin_three e x) =
      G.mbarZeroThree x := by
  let r := G.mbarZeroThree x
  have hx : G.mbarZeroThree.symm r = x := G.mbarZeroThree.symm_apply_apply x
  rw [← hx]
  have hr : G.mbarZeroThree.symm r = algebraMap R (C.H 0 (Fin 3)) r := by
    simpa only [Algebra.algebraMap_self, RingHom.id_apply]
      using G.mbarZeroThree.symm.commutes r
  rw [hr]
  simp only [AlgEquiv.commutes, Algebra.algebraMap_self, RingHom.id_apply]

/-- The scalar three-point correlator is invariant under every permutation of
its labels. -/
theorem threePoint_relabel (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (e : Equiv.Perm (Fin 3)) :
    (T.threePoint G).domDomCongr e = T.threePoint G := by
  ext a
  have h := congrArg (fun f ↦ f a)
    (T.relabel (Fin 3) (Fin 3) StableArity.zero_fin_three
      StableArity.zero_fin_three e)
  change C.rename 0 (Fin 3) (Fin 3) StableArity.zero_fin_three
      StableArity.zero_fin_three e
        (T.omega (Fin 3) StableArity.zero_fin_three (a ∘ e)) =
    T.omega (Fin 3) StableArity.zero_fin_three a at h
  change G.mbarZeroThree
      (T.omega (Fin 3) StableArity.zero_fin_three (a ∘ e)) =
    G.mbarZeroThree (T.omega (Fin 3) StableArity.zero_fin_three a)
  exact (G.mbarZeroThree_rename e _).symm.trans (congrArg G.mbarZeroThree h)

/-- Symmetry of the first two inputs of the three-point correlator. -/
theorem threePointFunction_swap_first (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x y z : V) :
    T.threePointFunction G x y z = T.threePointFunction G y x z := by
  let a : Fin 3 → V := Fin.cons x (Fin.cons y fun _ ↦ z)
  have h := congrArg (fun f ↦ f a)
    (T.threePoint_relabel G (Equiv.swap 0 1))
  rw [threePointFunction_apply, threePointFunction_apply]
  change (T.threePoint G) a =
    (T.threePoint G) (Fin.cons y (Fin.cons x fun _ ↦ z))
  change (T.threePoint G) (a ∘ Equiv.swap 0 1) = (T.threePoint G) a at h
  rw [← h]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Symmetry of the last two inputs of the three-point correlator. -/
theorem threePointFunction_swap_last (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x y z : V) :
    T.threePointFunction G x y z = T.threePointFunction G x z y := by
  let a : Fin 3 → V := Fin.cons x (Fin.cons y fun _ ↦ z)
  have h := congrArg (fun f ↦ f a)
    (T.threePoint_relabel G (Equiv.swap 1 2))
  rw [threePointFunction_apply, threePointFunction_apply]
  change (T.threePoint G) a =
    (T.threePoint G) (Fin.cons x (Fin.cons z fun _ ↦ y))
  change (T.threePoint G) (a ∘ Equiv.swap 1 2) = (T.threePoint G) a at h
  rw [← h]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The product extracted from a CohFT is commutative. -/
theorem product_comm (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x y : V) :
    T.product G x y = T.product G y x := by
  apply T.pairing.toDual.injective
  ext z
  simp only [T.pairing.toDual_apply, T.pairing_product]
  exact T.threePointFunction_swap_first G x y z

/-- Inserting the CohFT unit into the first three-point slot recovers the
metric. -/
theorem threePointFunction_unit (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x y : V) :
    T.threePointFunction G T.unit x y = T.pairing.form x y := by
  let a : Fin 3 → V := Fin.cons T.unit (Fin.cons x fun _ ↦ y)
  have h := congrArg (fun f ↦ f a)
    (T.relabel (Option (Fin 2)) (Fin 3) StableArity.zero_option_fin_two
      StableArity.zero_fin_three optionFinTwoEquivFinThree)
  rw [threePointFunction_apply]
  simp only [threePoint, LinearMap.compMultilinearMap_apply]
  change G.mbarZeroThree (T.omega (Fin 3) StableArity.zero_fin_three a) = _
  have hG := congrArg G.mbarZeroThree h
  rw [← hG]
  have hnorm := T.normalization ![x, y]
  change T.omega (Option (Fin 2)) StableArity.zero_option_fin_two
      (fun | none => T.unit | some i => ![x, y] i) = _ at hnorm
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.domDomCongr_apply]
  change G.mbarZeroThree
      (C.rename 0 (Option (Fin 2)) (Fin 3) StableArity.zero_option_fin_two
        StableArity.zero_fin_three optionFinTwoEquivFinThree
        (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two
          (a ∘ optionFinTwoEquivFinThree))) = _
  have ha : a ∘ optionFinTwoEquivFinThree =
      (fun | none => T.unit | some i => ![x, y] i) := by
    funext i
    rcases i with _ | i
    · rfl
    · fin_cases i <;> rfl
  rw [ha]
  rw [hnorm]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, AlgEquiv.commutes, Algebra.algebraMap_self,
    RingHom.id_apply]

/-- The CohFT unit is a left identity for the extracted product. -/
theorem unit_product (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x : V) :
    T.product G T.unit x = x := by
  apply T.pairing.toDual.injective
  ext y
  rw [T.pairing.toDual_apply, T.pairing.toDual_apply, T.pairing_product]
  exact T.threePointFunction_unit G x y

/-- The CohFT unit is a right identity for the extracted product. -/
theorem product_unit (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x : V) :
    T.product G x T.unit = x := by
  rw [T.product_comm G x T.unit, T.unit_product G x]

/-- The two genus-zero boundary presentations of the four-point class agree.
This is the cohomology-valued, basis-free WDVV identity. -/
theorem pairContractTarget_wdvv (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) :
    (T.pairing.pairContractTarget
        (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two)
        (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two)).domDomCongr
          wdvvPermutation =
      T.pairing.pairContractTarget
        (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two)
        (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two) := by
  ext a
  simp only [MultilinearMap.domDomCongr_apply]
  rw [T.separating]
  simp only [LinearMap.compMultilinearMap_apply]
  have hrel := congrArg (fun f ↦ f a)
    (T.relabel (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two) wdvvPermutation)
  change C.rename 0 (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two) wdvvPermutation
        (T.omega (Fin 2 ⊕ Fin 2)
          (StableArity.separating StableArity.zero_option_fin_two
            StableArity.zero_option_fin_two) (a ∘ wdvvPermutation)) =
    T.omega (Fin 2 ⊕ Fin 2)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two) a at hrel
  have hboundary := congrArg
    (fun f ↦ f (T.omega (Fin 2 ⊕ Fin 2)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two) (a ∘ wdvvPermutation)))
    G.mbarZeroFourBoundary
  exact hboundary.symm.trans
    (congrArg (C.separating 0 0 (Fin 2) (Fin 2)
      StableArity.zero_option_fin_two StableArity.zero_option_fin_two) hrel)

private noncomputable def threePointScalar (G : GenusZeroGeometry C) :
    C.H 0 (Option (Fin 2)) →ₐ[R] R :=
  G.mbarZeroThree.toAlgHom.comp
    (C.rename 0 (Option (Fin 2)) (Fin 3) StableArity.zero_option_fin_two
      StableArity.zero_fin_three optionFinTwoEquivFinThree).toAlgHom

private theorem threePointScalar_omega_apply (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (u x y : V) :
    threePointScalar G
        (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two
          (fun | none => u | some i => ![x, y] i)) =
      T.threePointFunction G u x y := by
  let a : Fin 3 → V := Fin.cons u (Fin.cons x fun _ ↦ y)
  have h := congrArg (fun f ↦ f a)
    (T.relabel (Option (Fin 2)) (Fin 3) StableArity.zero_option_fin_two
      StableArity.zero_fin_three optionFinTwoEquivFinThree)
  rw [threePointFunction_apply]
  simp only [threePointScalar, threePoint, AlgHom.comp_apply,
    LinearMap.compMultilinearMap_apply]
  change G.mbarZeroThree
      (C.rename 0 (Option (Fin 2)) (Fin 3) StableArity.zero_option_fin_two
        StableArity.zero_fin_three optionFinTwoEquivFinThree
        (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two
          (fun | none => u | some i => ![x, y] i))) =
    G.mbarZeroThree (T.omega (Fin 3) StableArity.zero_fin_three a)
  change C.rename 0 (Option (Fin 2)) (Fin 3) StableArity.zero_option_fin_two
      StableArity.zero_fin_three optionFinTwoEquivFinThree
        (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two
          (a ∘ optionFinTwoEquivFinThree)) =
    T.omega (Fin 3) StableArity.zero_fin_three a at h
  have ha : a ∘ optionFinTwoEquivFinThree =
      (fun | none => u | some i => ![x, y] i) := by
    funext i
    rcases i with _ | i
    · rfl
    · fin_cases i <;> rfl
  rw [ha] at h
  exact congrArg G.mbarZeroThree h

private theorem scalarized_pairContract_products
    (T : GenusZeroCohFT R V C) (G : GenusZeroGeometry C)
    (x y z w : V) :
    (Algebra.TensorProduct.lift (threePointScalar G) (threePointScalar G)
      (fun _ _ ↦ .all _ _))
        (T.pairing.pairContractTarget
          (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two)
          (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two)
          (Sum.elim ![x, y] ![z, w])) =
      T.pairing.form (T.product G x y) (T.product G z w) := by
  change ((Algebra.TensorProduct.lift (threePointScalar G) (threePointScalar G)
      (fun _ _ ↦ .all _ _)).toLinearMap.compMultilinearMap
        (T.pairing.pairContractTarget
          (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two)
          (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two)))
      (Sum.elim ![x, y] ![z, w]) = _
  rw [T.pairing.pairContractTarget_comp_lift]
  rw [SymmetricPerfectPairing.pairContract_apply,
    SymmetricPerfectPairing.contractTwo_apply]
  rw [← T.pairing.contract_toDual_mul_toDual
    (T.product G x y) (T.product G z w)]
  congr 1
  ext u v
  simp only [TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.restrictScalars_apply,
    TensorProduct.lift.tmul,
    SymmetricPerfectPairing.finTwoToBilin_apply,
    MultilinearMap.currySum_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.compl₂_apply, LinearMap.mul'_apply,
    LinearMap.comp_apply,
    T.pairing.toDual_apply]
  have hleft :
      (fun i₁ ↦ Sum.rec (Sum.elim ![x, y] ![z, w])
        (Fin.cons u fun _ ↦ v)
          (SymmetricPerfectPairing.separatingLabelsEquiv (Fin 2) (Fin 2)
            (.inl i₁))) =
        (fun | none => u | some i => ![x, y] i) := by
    funext i
    rcases i with _ | i
    · rfl
    · fin_cases i <;> rfl
  have hright :
      (fun i₂ ↦ Sum.rec (Sum.elim ![x, y] ![z, w])
        (Fin.cons u fun _ ↦ v)
          (SymmetricPerfectPairing.separatingLabelsEquiv (Fin 2) (Fin 2)
            (.inr i₂))) =
        (fun | none => v | some i => ![z, w] i) := by
    funext i
    rcases i with _ | i
    · rfl
    · fin_cases i <;> rfl
  rw [hleft, hright]
  change threePointScalar G
        (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two
          (fun | none => u | some i => ![x, y] i)) *
      threePointScalar G
        (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two
          (fun | none => v | some i => ![z, w] i)) =
    T.pairing.form (T.product G x y) u *
      T.pairing.form (T.product G z w) v
  rw [threePointScalar_omega_apply, threePointScalar_omega_apply]
  rw [T.threePointFunction_swap_first G u x y,
    T.threePointFunction_swap_last G x u y,
    ← T.pairing_product]
  rw [T.threePointFunction_swap_first G v z w,
    T.threePointFunction_swap_last G z v w,
    ← T.pairing_product]

/-- Scalar WDVV in basis-free form. -/
theorem pairing_products_wdvv (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x y z w : V) :
    T.pairing.form (T.product G x y) (T.product G z w) =
      T.pairing.form (T.product G x z) (T.product G y w) := by
  let a : Fin 2 ⊕ Fin 2 → V := Sum.elim ![x, y] ![z, w]
  have h := congrArg (fun f ↦ f a) (T.pairContractTarget_wdvv G)
  have hscalar := congrArg
    (Algebra.TensorProduct.lift (threePointScalar G) (threePointScalar G)
      (fun _ _ ↦ .all _ _)) h
  have ha : a ∘ wdvvPermutation = Sum.elim ![x, z] ![y, w] := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  simp only [MultilinearMap.domDomCongr_apply] at hscalar
  change (Algebra.TensorProduct.lift (threePointScalar G) (threePointScalar G)
      (fun _ _ ↦ .all _ _))
        (T.pairing.pairContractTarget
          (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two)
          (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two)
          (a ∘ wdvvPermutation)) =
    (Algebra.TensorProduct.lift (threePointScalar G) (threePointScalar G)
      (fun _ _ ↦ .all _ _))
        (T.pairing.pairContractTarget
          (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two)
          (T.omega (Option (Fin 2)) StableArity.zero_option_fin_two) a) at hscalar
  rw [ha] at hscalar
  rw [scalarized_pairContract_products T G x z y w,
    scalarized_pairContract_products T G x y z w] at hscalar
  exact hscalar.symm

/-- Frobenius invariance of the extracted metric and product. -/
theorem pairing_product_assoc (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x y z : V) :
    T.pairing.form (T.product G x y) z =
      T.pairing.form x (T.product G y z) := by
  rw [T.pairing_product]
  rw [T.pairing.isSymm.eq]
  rw [T.pairing_product]
  rw [T.threePointFunction_swap_first G x y z]
  exact T.threePointFunction_swap_last G y x z

/-- Associativity of the product extracted from the four-point boundary
relation. -/
theorem product_assoc (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x y z : V) :
    T.product G (T.product G x y) z = T.product G x (T.product G y z) := by
  apply T.pairing.toDual.injective
  ext w
  simp only [T.pairing.toDual_apply]
  calc
    T.pairing.form (T.product G (T.product G x y) z) w =
        T.pairing.form (T.product G x y) (T.product G z w) :=
      T.pairing_product_assoc G (T.product G x y) z w
    _ = T.pairing.form (T.product G y z) (T.product G x w) := by
      rw [T.product_comm G x y]
      exact (T.pairing_products_wdvv G y z x w).symm
    _ = T.pairing.form (T.product G (T.product G y z) x) w :=
      (T.pairing_product_assoc G (T.product G y z) x w).symm
    _ = T.pairing.form (T.product G x (T.product G y z)) w := by
      rw [T.product_comm G (T.product G y z) x]

/-- A separate carrier for the Frobenius algebra extracted from a genus-zero
theory. Its dependence on `T` and `G` prevents competing products from becoming
global instances on the original module. -/
def FrobeniusCarrier (_T : GenusZeroCohFT R V C) (_G : GenusZeroGeometry C) := V

namespace FrobeniusCarrier

variable (T : GenusZeroCohFT R V C) (G : GenusZeroGeometry C)

instance addCommGroup : AddCommGroup (FrobeniusCarrier T G) :=
  inferInstanceAs (AddCommGroup V)

instance module : Module R (FrobeniusCarrier T G) :=
  inferInstanceAs (Module R V)

instance free : Module.Free R (FrobeniusCarrier T G) :=
  inferInstanceAs (Module.Free R V)

instance finite : Module.Finite R (FrobeniusCarrier T G) :=
  inferInstanceAs (Module.Finite R V)

noncomputable instance commRing : CommRing (FrobeniusCarrier T G) where
  __ := addCommGroup T G
  mul x y := T.product G (show V from x) (show V from y)
  one := (show FrobeniusCarrier T G from T.unit)
  mul_assoc x y z := by
    change T.product G (T.product G (show V from x) (show V from y))
      (show V from z) = T.product G (show V from x)
        (T.product G (show V from y) (show V from z))
    exact T.product_assoc G (show V from x) (show V from y) (show V from z)
  one_mul x := by
    change T.product G T.unit (show V from x) = (show V from x)
    exact T.unit_product G (show V from x)
  mul_one x := by
    change T.product G (show V from x) T.unit = (show V from x)
    exact T.product_unit G (show V from x)
  zero_mul x := by
    change T.product G (0 : V) (show V from x) = 0
    exact LinearMap.congr_fun (T.product G).map_zero (show V from x)
  mul_zero x := by
    change T.product G (show V from x) 0 = 0
    exact (T.product G (show V from x)).map_zero
  left_distrib x y z := by
    change T.product G (show V from x) ((show V from y) + (show V from z)) =
      T.product G (show V from x) (show V from y) +
        T.product G (show V from x) (show V from z)
    exact (T.product G (show V from x)).map_add (show V from y) (show V from z)
  right_distrib x y z := by
    change T.product G ((show V from x) + (show V from y)) (show V from z) =
      T.product G (show V from x) (show V from z) +
        T.product G (show V from y) (show V from z)
    exact LinearMap.congr_fun
      ((T.product G).map_add (show V from x) (show V from y)) (show V from z)
  mul_comm x y := by
    change T.product G (show V from x) (show V from y) =
      T.product G (show V from y) (show V from x)
    exact T.product_comm G (show V from x) (show V from y)

noncomputable instance algebra : Algebra R (FrobeniusCarrier T G) :=
  Algebra.ofModule
    (fun r x y ↦ by
      change T.product G (r • (show V from x)) (show V from y) =
        r • T.product G (show V from x) (show V from y)
      exact LinearMap.congr_fun ((T.product G).map_smul r (show V from x))
        (show V from y))
    (fun r x y ↦ by
      change T.product G (show V from x) (r • (show V from y)) =
        r • T.product G (show V from x) (show V from y)
      exact (T.product G (show V from x)).map_smul r (show V from y))

/-- The identity linear equivalence from the extracted carrier to the original
state space. -/
def toStateSpace : FrobeniusCarrier T G ≃ₗ[R] V := LinearEquiv.refl R V

end FrobeniusCarrier

/-- Package the extracted product and metric as the project's existing
commutative Frobenius algebra. -/
noncomputable def toCommFrobeniusAlgebra (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) : CommFrobeniusAlgebra R (FrobeniusCarrier T G) where
  counit :=
    { toFun := fun x ↦ T.pairing.form (FrobeniusCarrier.toStateSpace T G x) T.unit
      map_add' := fun x y ↦ by
        exact LinearMap.congr_fun (T.pairing.form.map_add
          (FrobeniusCarrier.toStateSpace T G x)
          (FrobeniusCarrier.toStateSpace T G y)) T.unit
      map_smul' := fun r x ↦ by
        exact LinearMap.congr_fun (T.pairing.form.map_smul r
          (FrobeniusCarrier.toStateSpace T G x)) T.unit }
  isPerfPair := by
    have hform : tracePairing
        ({ toFun := fun x : FrobeniusCarrier T G ↦
             T.pairing.form (FrobeniusCarrier.toStateSpace T G x) T.unit
           map_add' := fun x y ↦ by
             exact LinearMap.congr_fun (T.pairing.form.map_add
               (FrobeniusCarrier.toStateSpace T G x)
               (FrobeniusCarrier.toStateSpace T G y)) T.unit
           map_smul' := fun r x ↦ by
             exact LinearMap.congr_fun (T.pairing.form.map_smul r
               (FrobeniusCarrier.toStateSpace T G x)) T.unit } :
          FrobeniusCarrier T G →ₗ[R] R) =
        T.pairing.form.compl₁₂ (FrobeniusCarrier.toStateSpace T G)
          (FrobeniusCarrier.toStateSpace T G) := by
      ext x y
      change T.pairing.form
        (T.product G (FrobeniusCarrier.toStateSpace T G x)
          (FrobeniusCarrier.toStateSpace T G y)) T.unit =
        T.pairing.form (FrobeniusCarrier.toStateSpace T G x)
          (FrobeniusCarrier.toStateSpace T G y)
      rw [T.pairing_product_assoc, T.product_unit]
    rw [hform]
    change (T.pairing.form.compl₁₂
      (FrobeniusCarrier.toStateSpace T G).toLinearMap
      (FrobeniusCarrier.toStateSpace T G).toLinearMap).IsPerfPair
    letI : T.pairing.form.IsPerfPair := T.pairing.isPerfPair
    infer_instance

/-- The Frobenius pairing recovered from the packaged algebra evaluates as the
original CohFT metric under the carrier identification. -/
theorem toCommFrobeniusAlgebra_pairing (T : GenusZeroCohFT R V C)
    (G : GenusZeroGeometry C) (x y : FrobeniusCarrier T G) :
    (T.toCommFrobeniusAlgebra G).pairing.form x y =
      T.pairing.form (FrobeniusCarrier.toStateSpace T G x)
        (FrobeniusCarrier.toStateSpace T G y) := by
  change T.pairing.form
    (T.product G (FrobeniusCarrier.toStateSpace T G x)
      (FrobeniusCarrier.toStateSpace T G y)) T.unit =
    T.pairing.form (FrobeniusCarrier.toStateSpace T G x)
      (FrobeniusCarrier.toStateSpace T G y)
  rw [T.pairing_product_assoc, T.product_unit]

/-- The correlators of the extracted Frobenius algebra recover the scalar
three-point correlator from which its multiplication was defined. -/
theorem toCommFrobeniusAlgebra_correlator_zero_fin_three
    (T : GenusZeroCohFT R V C) (G : GenusZeroGeometry C)
    (a : Fin 3 → FrobeniusCarrier T G) :
    (T.toCommFrobeniusAlgebra G).correlator 0 (Fin 3) a =
      T.threePoint G (fun i ↦ FrobeniusCarrier.toStateSpace T G (a i)) := by
  rw [(T.toCommFrobeniusAlgebra G).correlator_zero_fin_three_apply]
  rw [T.toCommFrobeniusAlgebra_pairing]
  change T.pairing.form
      (T.product G (FrobeniusCarrier.toStateSpace T G (a 0))
        (FrobeniusCarrier.toStateSpace T G (a 1)))
      (FrobeniusCarrier.toStateSpace T G (a 2)) = _
  rw [T.pairing_product, T.threePointFunction_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

end GenusZeroCohFT

end AxiomaticGW
