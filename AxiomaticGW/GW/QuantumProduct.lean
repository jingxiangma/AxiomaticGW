/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.Novikov
public import AxiomaticGW.GW.Basic

/-!
# Quantum products

The curve-class theory determines one three-point product coefficient for each
effective class. A quantum-product family packages the resulting small product
and its big deformations; its WDVV identity implies associativity.
-/

@[expose] public section

namespace AxiomaticGW

universe u

namespace CurveClassGW

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R}

/-- The scalar genus-zero three-point class in curve class `beta`. -/
noncomputable def threePoint (Omega : CurveClassGW R V B D C)
    (G : GenusZeroGeometry C) (beta : B) :
    MultilinearMap R (fun _ : Fin 3 ↦ V) R :=
  G.mbarZeroThree.toLinearMap.compMultilinearMap
    (Omega.omega 0 (Fin 3) StableArity.zero_fin_three beta)

/-- Raise the last input of a fixed three-point coefficient with the metric. -/
noncomputable def smallProductCoefficient (Omega : CurveClassGW R V B D C)
    (G : GenusZeroGeometry C) (beta : B) : V →ₗ[R] V →ₗ[R] V :=
  (LinearMap.compRight R
      (LinearMap.compRight R Omega.pairing.toDual.symm.toLinearMap)).comp
    ((LinearMap.compRight R
      (SymmetricPerfectPairing.finTwoToBilin (R := R) (V := V))).comp
        (multilinearCurryLeftEquiv R (fun _ : Fin 3 ↦ V) R).toLinearMap) <|
          Omega.threePoint G beta

/-- The coefficient product is characterized by the beta-resolved
three-point invariant. -/
theorem pairing_smallProductCoefficient (Omega : CurveClassGW R V B D C)
    (G : GenusZeroGeometry C) (beta : B) (x y z : V) :
    Omega.pairing.form (Omega.smallProductCoefficient G beta x y) z =
      Omega.threePoint G beta (Fin.cons x (Fin.cons y fun _ ↦ z)) := by
  rw [← Omega.pairing.toDual_apply]
  simp [smallProductCoefficient, SymmetricPerfectPairing.finTwoToBilin_apply]

/-- The small quantum product of two ordinary states, retained coefficientwise
as a Novikov series with values in the state space. -/
noncomputable def smallProductSeries (Omega : CurveClassGW R V B D C)
    (G : GenusZeroGeometry C) (x y : V) : NovikovSeries D V :=
  fun beta ↦ Omega.smallProductCoefficient G beta x y

@[simp]
theorem smallProductSeries_apply (Omega : CurveClassGW R V B D C)
    (G : GenusZeroGeometry C) (x y : V) (beta : B) :
    Omega.smallProductSeries G x y beta =
      Omega.smallProductCoefficient G beta x y := rfl

end CurveClassGW

/-- A small quantum product and its big deformations, expressed over any
coefficient ring. WDVV is kept in its four-input metric form. -/
structure QuantumProductFamily (Lambda W : Type*) [CommRing Lambda]
    [AddCommGroup W] [Module Lambda W]
    (pairing : SymmetricPerfectPairing Lambda W) where
  /-- Product at the deformation point `t`; `t = 0` is the small product. -/
  product : W → W →ₗ[Lambda] W →ₗ[Lambda] W
  /-- Flat identity. -/
  unit : W
  /-- Quantum products are commutative. -/
  product_comm : ∀ t x y, product t x y = product t y x
  /-- The flat identity remains a unit at every deformation point. -/
  unit_product : ∀ t x, product t unit x = x
  /-- Invariance of the metric. -/
  pairing_product : ∀ t x y z,
    pairing.form (product t x y) z = pairing.form x (product t y z)
  /-- WDVV in the two boundary presentations of the four-point function. -/
  wdvv : ∀ t x y z w,
    pairing.form (product t x y) (product t z w) =
      pairing.form (product t x z) (product t y w)

namespace QuantumProductFamily

variable {Lambda W : Type*} [CommRing Lambda]
  [AddCommGroup W] [Module Lambda W]
  {pairing : SymmetricPerfectPairing Lambda W}

/-- The flat identity is also a right identity by commutativity. -/
theorem product_unit (Q : QuantumProductFamily Lambda W pairing)
    (t x : W) : Q.product t x Q.unit = x := by
  rw [Q.product_comm t x Q.unit, Q.unit_product t x]

/-- WDVV and metric nondegeneracy imply associativity at every big quantum
deformation point. -/
theorem product_assoc (Q : QuantumProductFamily Lambda W pairing)
    (t x y z : W) :
    Q.product t (Q.product t x y) z =
      Q.product t x (Q.product t y z) := by
  apply pairing.toDual.injective
  ext w
  simp only [pairing.toDual_apply]
  calc
    pairing.form (Q.product t (Q.product t x y) z) w =
        pairing.form (Q.product t x y) (Q.product t z w) :=
      Q.pairing_product t (Q.product t x y) z w
    _ = pairing.form (Q.product t x y) (Q.product t w z) := by
      rw [Q.product_comm t z w]
    _ = pairing.form (Q.product t x w) (Q.product t y z) :=
      Q.wdvv t x y w z
    _ = pairing.form (Q.product t y z) (Q.product t x w) :=
      by simpa using pairing.isSymm.eq (Q.product t x w) (Q.product t y z)
    _ = pairing.form (Q.product t (Q.product t y z) x) w :=
      (Q.pairing_product t (Q.product t y z) x w).symm
    _ = pairing.form (Q.product t x (Q.product t y z)) w := by
      rw [Q.product_comm t (Q.product t y z) x]

/-- The small quantum product is the family member at the origin. -/
def smallProduct (Q : QuantumProductFamily Lambda W pairing) : W →ₗ[Lambda] W →ₗ[Lambda] W :=
  Q.product 0

/-- The small quantum product is associative. -/
theorem smallProduct_assoc (Q : QuantumProductFamily Lambda W pairing)
    (x y z : W) :
    Q.smallProduct (Q.smallProduct x y) z =
      Q.smallProduct x (Q.smallProduct y z) :=
  Q.product_assoc 0 x y z

end QuantumProductFamily

end AxiomaticGW
