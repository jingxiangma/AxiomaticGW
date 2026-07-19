/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.Novikov
public import AxiomaticGW.CohFT.Frobenius
public import AxiomaticGW.GW.Basic

/-!
# Small quantum product

For each effective curve class, the genus-zero Gromov--Witten theory determines
a three-point invariant. Separating gluing and the four-point boundary relation
imply coefficientwise WDVV and associativity of the resulting small quantum product.
-/

@[expose] public section

namespace AxiomaticGW

universe u

namespace GromovWittenTheory

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R}

private def optionFinTwoEquivFinThree : Option (Fin 2) ≃ Fin 3 :=
  (finSuccEquiv 2).symm

/-- The scalar genus-zero three-point class in curve class `beta`. -/
def threePoint (Omega : GromovWittenTheory R V B D C)
    (G : GenusZeroGeometry C) (beta : B) :
    MultilinearMap R (fun _ : Fin 3 ↦ V) R :=
  G.mbarZeroThree.toLinearMap.compMultilinearMap
    (Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta)

/-- Raise the last input of a fixed three-point coefficient with the metric. -/
noncomputable def smallQuantumProductCoefficient (Omega : GromovWittenTheory R V B D C)
    (G : GenusZeroGeometry C) (beta : B) : V →ₗ[R] V →ₗ[R] V :=
  (LinearMap.compRight R
      (LinearMap.compRight R Omega.pairing.toDual.symm.toLinearMap)).comp
    ((LinearMap.compRight R
      (SymmetricPerfectPairing.finTwoToBilin (R := R) (V := V))).comp
        (multilinearCurryLeftEquiv R (fun _ : Fin 3 ↦ V) R).toLinearMap) <|
          Omega.threePoint G beta

/-- The fixed-class contribution to the small quantum product is characterized
by the corresponding three-point Gromov--Witten invariant. -/
theorem pairing_smallQuantumProductCoefficient (Omega : GromovWittenTheory R V B D C)
    (G : GenusZeroGeometry C) (beta : B) (x y z : V) :
    Omega.pairing.form (Omega.smallQuantumProductCoefficient G beta x y) z =
      Omega.threePoint G beta (Fin.cons x (Fin.cons y fun _ ↦ z)) := by
  rw [← Omega.pairing.toDual_apply]
  simp only [smallQuantumProductCoefficient, Nat.succ_eq_add_one,
    Nat.reduceAdd, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, multilinearCurryLeftEquiv_apply,
    LinearMap.compRight_apply, LinearEquiv.apply_symm_apply,
    SymmetricPerfectPairing.finTwoToBilin_apply,
    MultilinearMap.curryLeft_apply]

/-- The small quantum product of two ordinary states, retained coefficientwise
as a Novikov series with values in the state space. -/
noncomputable def smallQuantumProduct (Omega : GromovWittenTheory R V B D C)
    (G : GenusZeroGeometry C) (x y : V) : NovikovSeries D V :=
  fun beta ↦ Omega.smallQuantumProductCoefficient G beta x y

@[simp]
theorem smallQuantumProduct_apply (Omega : GromovWittenTheory R V B D C)
    (G : GenusZeroGeometry C) (x y : V) (beta : B) :
    Omega.smallQuantumProduct G x y beta =
      Omega.smallQuantumProductCoefficient G beta x y := rfl

/-- The two four-point boundary presentations agree after summing over all
splittings of a fixed curve class. This is coefficientwise, cohomology-valued
WDVV. -/
theorem pairContractTarget_wdvv (Omega : GromovWittenTheory R V B D C)
    (G : GenusZeroGeometry C) (beta : B) :
    ((∑ split ∈ D.splittings beta,
        Omega.pairing.pairContractTarget
          (Omega.omega 0 (Option (Fin 2))
            StableArity.zero_option_fin_two split.1)
          (Omega.omega 0 (Option (Fin 2))
            StableArity.zero_option_fin_two split.2)).domDomCongr
      wdvvPermutation) =
      ∑ split ∈ D.splittings beta,
        Omega.pairing.pairContractTarget
          (Omega.omega 0 (Option (Fin 2))
            StableArity.zero_option_fin_two split.1)
          (Omega.omega 0 (Option (Fin 2))
            StableArity.zero_option_fin_two split.2) := by
  ext a
  simp only [MultilinearMap.domDomCongr_apply]
  rw [Omega.separating]
  simp only [LinearMap.compMultilinearMap_apply]
  have hrel := congrArg (fun f ↦ f a)
    (Omega.relabel 0 (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two) wdvvPermutation beta)
  change C.rename 0 (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two) wdvvPermutation
        (Omega.omega 0 (Fin 2 ⊕ Fin 2)
          (StableArity.separating StableArity.zero_option_fin_two
            StableArity.zero_option_fin_two) beta (a ∘ wdvvPermutation)) =
    Omega.omega 0 (Fin 2 ⊕ Fin 2)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two) beta a at hrel
  have hboundary := congrArg
    (fun f ↦ f (Omega.omega 0 (Fin 2 ⊕ Fin 2)
      (StableArity.separating StableArity.zero_option_fin_two
        StableArity.zero_option_fin_two) beta (a ∘ wdvvPermutation)))
    G.mbarZeroFourBoundary
  exact hboundary.symm.trans
    (congrArg (C.separating 0 0 (Fin 2) (Fin 2)
      StableArity.zero_option_fin_two StableArity.zero_option_fin_two) hrel)

/-- The scalar three-point coefficient is invariant under relabelling. -/
theorem threePoint_relabel (Omega : GromovWittenTheory R V B D C)
    (G : GenusZeroGeometry C) (beta : B) (e : Equiv.Perm (Fin 3)) :
    (Omega.threePoint G beta).domDomCongr e = Omega.threePoint G beta := by
  ext a
  have h := congrArg (fun f ↦ f a)
    (Omega.relabel 0 (Fin 3) (Fin 3) StableArity.zero_fin_three
      StableArity.zero_fin_three e beta)
  change C.rename 0 (Fin 3) (Fin 3) StableArity.zero_fin_three
      StableArity.zero_fin_three e
        (Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta (a ∘ e)) =
    Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta a at h
  change G.mbarZeroThree
      (Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta (a ∘ e)) =
    G.mbarZeroThree
      (Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta a)
  exact (G.mbarZeroThree_rename e _).symm.trans
    (congrArg G.mbarZeroThree h)

/-- Symmetry of the first two inputs of a three-point GW coefficient. -/
theorem threePoint_swap_first (Omega : GromovWittenTheory R V B D C)
    (G : GenusZeroGeometry C) (beta : B) (x y z : V) :
    Omega.threePoint G beta (Fin.cons x (Fin.cons y fun _ ↦ z)) =
      Omega.threePoint G beta (Fin.cons y (Fin.cons x fun _ ↦ z)) := by
  let a : Fin 3 → V := Fin.cons x (Fin.cons y fun _ ↦ z)
  have h := congrArg (fun f ↦ f a)
    (Omega.threePoint_relabel G beta (Equiv.swap 0 1))
  change Omega.threePoint G beta (a ∘ Equiv.swap 0 1) =
    Omega.threePoint G beta a at h
  rw [← h]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Symmetry of the last two inputs of a three-point GW coefficient. -/
theorem threePoint_swap_last (Omega : GromovWittenTheory R V B D C)
    (G : GenusZeroGeometry C) (beta : B) (x y z : V) :
    Omega.threePoint G beta (Fin.cons x (Fin.cons y fun _ ↦ z)) =
      Omega.threePoint G beta (Fin.cons x (Fin.cons z fun _ ↦ y)) := by
  let a : Fin 3 → V := Fin.cons x (Fin.cons y fun _ ↦ z)
  have h := congrArg (fun f ↦ f a)
    (Omega.threePoint_relabel G beta (Equiv.swap 1 2))
  change Omega.threePoint G beta (a ∘ Equiv.swap 1 2) =
    Omega.threePoint G beta a at h
  rw [← h]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Every fixed-class contribution to the small quantum product is commutative. -/
theorem smallQuantumProductCoefficient_comm
    (Omega : GromovWittenTheory R V B D C) (G : GenusZeroGeometry C)
    (beta : B) (x y : V) :
    Omega.smallQuantumProductCoefficient G beta x y =
      Omega.smallQuantumProductCoefficient G beta y x := by
  apply Omega.pairing.toDual.injective
  ext z
  simp only [Omega.pairing.toDual_apply,
    Omega.pairing_smallQuantumProductCoefficient]
  exact Omega.threePoint_swap_first G beta x y z

/-- Frobenius invariance holds coefficientwise. -/
theorem pairing_smallQuantumProductCoefficient_assoc
    (Omega : GromovWittenTheory R V B D C) (G : GenusZeroGeometry C)
    (beta : B) (x y z : V) :
    Omega.pairing.form (Omega.smallQuantumProductCoefficient G beta x y) z =
      Omega.pairing.form x (Omega.smallQuantumProductCoefficient G beta y z) := by
  rw [Omega.pairing_smallQuantumProductCoefficient]
  rw [Omega.pairing.isSymm.eq]
  rw [Omega.pairing_smallQuantumProductCoefficient]
  exact (Omega.threePoint_swap_first G beta x y z).trans
    (Omega.threePoint_swap_last G beta y x z)

/-- The beta-zero three-point coefficient with a unit insertion is the
metric. -/
theorem threePoint_unit_zero (Omega : GromovWittenTheory R V B D C)
    (G : GenusZeroGeometry C) (x y : V) :
    Omega.threePoint G 0
        (Fin.cons Omega.unit (Fin.cons x fun _ ↦ y)) =
      Omega.pairing.form x y := by
  let a : Fin 3 → V := Fin.cons Omega.unit (Fin.cons x fun _ ↦ y)
  have h := congrArg (fun f ↦ f a)
    (Omega.relabel 0 (Option (Fin 2)) (Fin 3)
      StableArity.zero_option_fin_two StableArity.zero_fin_three
      optionFinTwoEquivFinThree 0)
  simp only [threePoint, LinearMap.compMultilinearMap_apply]
  change G.mbarZeroThree
      (Omega.omega 0 (Fin 3) StableArity.zero_fin_three 0 a) = _
  have hG := congrArg G.mbarZeroThree h
  rw [← hG]
  have ha : a ∘ optionFinTwoEquivFinThree =
      (fun | none => Omega.unit | some i => ![x, y] i) := by
    funext i
    rcases i with _ | i
    · rfl
    · fin_cases i <;> rfl
  simp only [LinearMap.compMultilinearMap_apply,
    MultilinearMap.domDomCongr_apply]
  rw [show (fun i ↦ a (optionFinTwoEquivFinThree i)) =
    (fun | none => Omega.unit | some i => ![x, y] i) by exact ha]
  exact (congrArg
    (fun q ↦ G.mbarZeroThree
      (C.rename 0 (Option (Fin 2)) (Fin 3)
        StableArity.zero_option_fin_two StableArity.zero_fin_three
        optionFinTwoEquivFinThree q))
    (Omega.normalization_zero ![x, y])).trans
      (by simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, AlgEquiv.commutes, Algebra.algebraMap_self,
        RingHom.id_apply])

/-- Positive curve-class three-point coefficients vanish after a unit
insertion. -/
theorem threePoint_unit_of_ne (Omega : GromovWittenTheory R V B D C)
    (G : GenusZeroGeometry C) {beta : B} (hbeta : beta ≠ 0)
    (x y : V) :
    Omega.threePoint G beta
        (Fin.cons Omega.unit (Fin.cons x fun _ ↦ y)) = 0 := by
  let a : Fin 3 → V := Fin.cons Omega.unit (Fin.cons x fun _ ↦ y)
  have h := congrArg (fun f ↦ f a)
    (Omega.relabel 0 (Option (Fin 2)) (Fin 3)
      StableArity.zero_option_fin_two StableArity.zero_fin_three
      optionFinTwoEquivFinThree beta)
  simp only [threePoint, LinearMap.compMultilinearMap_apply]
  change G.mbarZeroThree
      (Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta a) = 0
  have hG := congrArg G.mbarZeroThree h
  rw [← hG]
  have ha : a ∘ optionFinTwoEquivFinThree =
      (fun | none => Omega.unit | some i => ![x, y] i) := by
    funext i
    rcases i with _ | i
    · rfl
    · fin_cases i <;> rfl
  simp only [LinearMap.compMultilinearMap_apply,
    MultilinearMap.domDomCongr_apply]
  rw [show (fun i ↦ a (optionFinTwoEquivFinThree i)) =
    (fun | none => Omega.unit | some i => ![x, y] i) by exact ha]
  exact (congrArg
    (fun q ↦ G.mbarZeroThree
      (C.rename 0 (Option (Fin 2)) (Fin 3)
        StableArity.zero_option_fin_two StableArity.zero_fin_three
        optionFinTwoEquivFinThree q))
    (Omega.normalization_nonzero beta hbeta ![x, y])).trans
      (by simp only [map_zero])

/-- The beta-zero product coefficient has the flat unit. -/
theorem unit_smallQuantumProductCoefficient_zero
    (Omega : GromovWittenTheory R V B D C) (G : GenusZeroGeometry C)
    (x : V) : Omega.smallQuantumProductCoefficient G 0 Omega.unit x = x := by
  apply Omega.pairing.toDual.injective
  ext y
  rw [Omega.pairing.toDual_apply, Omega.pairing.toDual_apply,
    Omega.pairing_smallQuantumProductCoefficient]
  exact Omega.threePoint_unit_zero G x y

/-- Positive product coefficients vanish after inserting the flat unit. -/
theorem unit_smallQuantumProductCoefficient_of_ne
    (Omega : GromovWittenTheory R V B D C) (G : GenusZeroGeometry C)
    {beta : B} (hbeta : beta ≠ 0) (x : V) :
    Omega.smallQuantumProductCoefficient G beta Omega.unit x = 0 := by
  apply Omega.pairing.toDual.injective
  ext y
  rw [Omega.pairing.toDual_apply, Omega.pairing.toDual_apply,
    Omega.pairing_smallQuantumProductCoefficient, map_zero]
  exact Omega.threePoint_unit_of_ne G hbeta x y

/-- The completed small quantum product has only its zero curve-class
coefficient after inserting the flat unit. -/
theorem smallQuantumProduct_unit
    (Omega : GromovWittenTheory R V B D C) (G : GenusZeroGeometry C)
    [DecidableEq B] (x : V) (beta : B) :
    Omega.smallQuantumProduct G Omega.unit x beta =
      if beta = 0 then x else 0 := by
  classical
  by_cases hbeta : beta = 0
  · subst beta
    rw [if_pos rfl, Omega.smallQuantumProduct_apply,
      Omega.unit_smallQuantumProductCoefficient_zero G]
  · rw [if_neg hbeta, Omega.smallQuantumProduct_apply,
      Omega.unit_smallQuantumProductCoefficient_of_ne G hbeta]

private def threePointScalar (G : GenusZeroGeometry C) :
    C.H 0 (Option (Fin 2)) →ₐ[R] R :=
  G.mbarZeroThree.toAlgHom.comp
    (C.rename 0 (Option (Fin 2)) (Fin 3) StableArity.zero_option_fin_two
      StableArity.zero_fin_three optionFinTwoEquivFinThree).toAlgHom

private theorem threePointScalar_omega_apply
    (Omega : GromovWittenTheory R V B D C) (G : GenusZeroGeometry C)
    (beta : B) (u x y : V) :
    threePointScalar G
        (Omega.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two beta
          (fun | none => u | some i => ![x, y] i)) =
      Omega.threePoint G beta (Fin.cons u (Fin.cons x fun _ ↦ y)) := by
  let a : Fin 3 → V := Fin.cons u (Fin.cons x fun _ ↦ y)
  have h := congrArg (fun f ↦ f a)
    (Omega.relabel 0 (Option (Fin 2)) (Fin 3)
      StableArity.zero_option_fin_two StableArity.zero_fin_three
      optionFinTwoEquivFinThree beta)
  simp only [threePointScalar, threePoint, AlgHom.comp_apply,
    LinearMap.compMultilinearMap_apply]
  change G.mbarZeroThree
      (C.rename 0 (Option (Fin 2)) (Fin 3) StableArity.zero_option_fin_two
        StableArity.zero_fin_three optionFinTwoEquivFinThree
        (Omega.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two beta
          (fun | none => u | some i => ![x, y] i))) =
    G.mbarZeroThree
      (Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta a)
  change C.rename 0 (Option (Fin 2)) (Fin 3)
      StableArity.zero_option_fin_two StableArity.zero_fin_three
      optionFinTwoEquivFinThree
        (Omega.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two beta
          (a ∘ optionFinTwoEquivFinThree)) =
    Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta a at h
  have ha : a ∘ optionFinTwoEquivFinThree =
      (fun | none => u | some i => ![x, y] i) := by
    funext i
    rcases i with _ | i
    · rfl
    · fin_cases i <;> rfl
  rw [ha] at h
  exact congrArg G.mbarZeroThree h

private theorem scalarized_pairContract_products
    (Omega : GromovWittenTheory R V B D C) (G : GenusZeroGeometry C)
    (beta₁ beta₂ : B) (x y z w : V) :
    (Algebra.TensorProduct.lift (threePointScalar G) (threePointScalar G)
      (fun _ _ ↦ .all _ _))
        (Omega.pairing.pairContractTarget
          (Omega.omega 0 (Option (Fin 2))
            StableArity.zero_option_fin_two beta₁)
          (Omega.omega 0 (Option (Fin 2))
            StableArity.zero_option_fin_two beta₂)
          (Sum.elim ![x, y] ![z, w])) =
      Omega.pairing.form
        (Omega.smallQuantumProductCoefficient G beta₁ x y)
        (Omega.smallQuantumProductCoefficient G beta₂ z w) := by
  change ((Algebra.TensorProduct.lift (threePointScalar G) (threePointScalar G)
      (fun _ _ ↦ .all _ _)).toLinearMap.compMultilinearMap
        (Omega.pairing.pairContractTarget
          (Omega.omega 0 (Option (Fin 2))
            StableArity.zero_option_fin_two beta₁)
          (Omega.omega 0 (Option (Fin 2))
            StableArity.zero_option_fin_two beta₂)))
      (Sum.elim ![x, y] ![z, w]) = _
  rw [Omega.pairing.pairContractTarget_comp_lift]
  rw [SymmetricPerfectPairing.pairContract_apply,
    SymmetricPerfectPairing.contractTwo_apply]
  rw [← Omega.pairing.contract_toDual_mul_toDual
    (Omega.smallQuantumProductCoefficient G beta₁ x y)
    (Omega.smallQuantumProductCoefficient G beta₂ z w)]
  congr 1
  ext u v
  simp only [TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.restrictScalars_apply,
    TensorProduct.lift.tmul,
    SymmetricPerfectPairing.finTwoToBilin_apply,
    MultilinearMap.currySum_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.compl₂_apply, LinearMap.mul'_apply, LinearMap.comp_apply,
    Omega.pairing.toDual_apply]
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
        (Omega.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two beta₁
          (fun | none => u | some i => ![x, y] i)) *
      threePointScalar G
        (Omega.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two beta₂
          (fun | none => v | some i => ![z, w] i)) =
    Omega.pairing.form (Omega.smallQuantumProductCoefficient G beta₁ x y) u *
      Omega.pairing.form (Omega.smallQuantumProductCoefficient G beta₂ z w) v
  rw [threePointScalar_omega_apply, threePointScalar_omega_apply]
  rw [Omega.threePoint_swap_first G beta₁ u x y,
    Omega.threePoint_swap_last G beta₁ x u y,
    ← Omega.pairing_smallQuantumProductCoefficient]
  rw [Omega.threePoint_swap_first G beta₂ v z w,
    Omega.threePoint_swap_last G beta₂ z v w,
    ← Omega.pairing_smallQuantumProductCoefficient]

/-- Scalar coefficientwise WDVV. The finite sums are exactly the coefficient
of the two Novikov products at `beta`. -/
theorem smallQuantumProductCoefficient_wdvv
    (Omega : GromovWittenTheory R V B D C) (G : GenusZeroGeometry C)
    (beta : B) (x y z w : V) :
    (∑ split ∈ D.splittings beta,
      Omega.pairing.form
        (Omega.smallQuantumProductCoefficient G split.1 x y)
        (Omega.smallQuantumProductCoefficient G split.2 z w)) =
      ∑ split ∈ D.splittings beta,
        Omega.pairing.form
          (Omega.smallQuantumProductCoefficient G split.1 x z)
          (Omega.smallQuantumProductCoefficient G split.2 y w) := by
  let a : Fin 2 ⊕ Fin 2 → V := Sum.elim ![x, y] ![z, w]
  have h := congrArg (fun f ↦ f a) (Omega.pairContractTarget_wdvv G beta)
  have hscalar := congrArg
    (Algebra.TensorProduct.lift (threePointScalar G) (threePointScalar G)
      (fun _ _ ↦ .all _ _)) h
  have ha : a ∘ wdvvPermutation = Sum.elim ![x, z] ![y, w] := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  simp only [MultilinearMap.domDomCongr_apply] at hscalar
  rw [show (fun i ↦ a (wdvvPermutation i)) =
    Sum.elim ![x, z] ![y, w] by exact ha] at hscalar
  simp only [_root_.sum_apply] at hscalar
  dsimp only [a] at hscalar
  simpa only [map_sum, scalarized_pairContract_products] using hscalar.symm

/-- Associativity of the small quantum product, stated at every Novikov
coefficient. The two finite sums are the coefficients of `(x * y) * z` and
`x * (y * z)`. -/
theorem smallQuantumProductCoefficient_assoc
    (Omega : GromovWittenTheory R V B D C) (G : GenusZeroGeometry C)
    (beta : B) (x y z : V) :
    (∑ split ∈ D.splittings beta,
      Omega.smallQuantumProductCoefficient G split.2
        (Omega.smallQuantumProductCoefficient G split.1 x y) z) =
      ∑ split ∈ D.splittings beta,
        Omega.smallQuantumProductCoefficient G split.2 x
          (Omega.smallQuantumProductCoefficient G split.1 y z) := by
  apply Omega.pairing.toDual.injective
  ext w
  rw [Omega.pairing.toDual_apply, Omega.pairing.toDual_apply]
  simp only [map_sum, LinearMap.sum_apply]
  calc
    (∑ split ∈ D.splittings beta,
        Omega.pairing.form
          (Omega.smallQuantumProductCoefficient G split.2
            (Omega.smallQuantumProductCoefficient G split.1 x y) z) w) =
      ∑ split ∈ D.splittings beta,
        Omega.pairing.form
          (Omega.smallQuantumProductCoefficient G split.1 x y)
          (Omega.smallQuantumProductCoefficient G split.2 z w) := by
        apply Finset.sum_congr rfl
        intro split _
        exact Omega.pairing_smallQuantumProductCoefficient_assoc G split.2
          (Omega.smallQuantumProductCoefficient G split.1 x y) z w
    _ = ∑ split ∈ D.splittings beta,
        Omega.pairing.form
          (Omega.smallQuantumProductCoefficient G split.1 y z)
          (Omega.smallQuantumProductCoefficient G split.2 x w) := by
        rw [Omega.smallQuantumProductCoefficient_wdvv G beta y z x w]
        apply Finset.sum_congr rfl
        intro split _
        rw [Omega.smallQuantumProductCoefficient_comm G split.1 y x]
    _ = ∑ split ∈ D.splittings beta,
        Omega.pairing.form
          (Omega.smallQuantumProductCoefficient G split.2 x
            (Omega.smallQuantumProductCoefficient G split.1 y z)) w := by
        apply Finset.sum_congr rfl
        intro split _
        let q := Omega.smallQuantumProductCoefficient G split.1 y z
        calc
          Omega.pairing.form q
              (Omega.smallQuantumProductCoefficient G split.2 x w) =
              Omega.pairing.form
                (Omega.smallQuantumProductCoefficient G split.2 q x) w :=
            (Omega.pairing_smallQuantumProductCoefficient_assoc G split.2
              q x w).symm
          _ = Omega.pairing.form
              (Omega.smallQuantumProductCoefficient G split.2 x q) w := by
            rw [Omega.smallQuantumProductCoefficient_comm G split.2 q x]

end GromovWittenTheory

end AxiomaticGW
