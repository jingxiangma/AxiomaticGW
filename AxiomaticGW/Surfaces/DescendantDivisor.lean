/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.DegreeZero
public import AxiomaticGW.Surfaces.Contraction
public import AxiomaticGW.GW.Descendants.DivisorAction
public import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# The surface descendant divisor action is the classical cup product

The classical cubic already follows from string, the identified surface
metric and grading. Extend that result from basis labels to arbitrary
states by multilinearity, then apply the four-point comparison of string
and divisor. This proves cup-product compatibility without adding a new
geometric hypothesis or changing the existing divisor-law interface.
-/

@[expose] public section

namespace AxiomaticGW

/-- Enumerate each element of a finite label type exactly once. -/
private def univOccurrences (S : Type) [Fintype S] [DecidableEq S] :
    (Finset.univ : Finset S).val ≃ S where
  toFun := (↑)
  invFun s := ⟨s, ⟨0, by
    rw [Multiset.count_eq_one_of_mem (Finset.univ.nodup) (Finset.mem_univ_val s)]
    omega⟩⟩
  left_inv := by
    rintro ⟨s, i⟩
    apply congrArg (fun j : Fin ((Finset.univ : Finset S).val.count s) ↦
      (⟨s, j⟩ : (Finset.univ : Finset S).val))
    apply Fin.ext
    change 0 = i.val
    have h := i.isLt
    have hc := Multiset.count_eq_one_of_mem (Finset.univ.nodup) (Finset.mem_univ_val s)
    omega
  right_inv _ := rfl

namespace SurfacePrimary
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Evaluate a labelled primary family through its multiset of basis states. -/
theorem eval_labels (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (S : Type) [Fintype S]
    (a : S → SurfaceBasisLabel X) :
    U.invariant g S beta (fun _ ↦ 0) (fun s ↦ (a s).value) =
      eval U g beta ((Finset.univ : Finset S).val.map a) := by
  classical
  rw [eval_map, invariant_relabel U g beta _ _ (univOccurrences S)]
  rfl

/-- The original classical cubic theorem extends to arbitrary linear combinations
of surface basis states at any three-element marking type. -/
theorem invariant_zero_cubic (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    (S : Type) [Fintype S] (hcard : Fintype.card S = 3)
    (a : S → SurfaceCohomology X.blowups) :
    U.invariant 0 S 0 (fun _ ↦ 0) a = SurfaceCohomology.counit X.blowups (∏ s, a s) := by
  classical
  let basis := (SurfaceCohomology.basis X.blowups).reindex (SurfaceBasisLabel.indexEquiv X).symm
  have hb (i : SurfaceBasisLabel X) : basis i = i.value := by
    cases i <;> simp only [basis, Module.Basis.reindex_apply, Equiv.symm_symm,
      SurfaceBasisLabel.indexEquiv, Equiv.coe_fn_mk, SurfaceBasisLabel.value,
      SurfaceCohomology.basis_unit, SurfaceCohomology.basis_hyperplane,
      SurfaceCohomology.basis_exceptional, SurfaceCohomology.basis_point]
  have heq : U.invariantMap 0 S 0 (fun _ ↦ 0) =
      (SurfaceCohomology.counit X.blowups).compMultilinearMap
        (MultilinearMap.mkPiAlgebra ℚ S (SurfaceCohomology X.blowups)) := by
    apply Module.Basis.ext_multilinear (fun _ ↦ basis)
    intro labels
    simp only [hb, U.invariantMap_apply, LinearMap.compMultilinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply]
    rw [eval_labels, eval_genus_zero_zero U T laws]
    simp only [classicalValue, Multiset.card_map, Finset.card_val, Finset.card_univ,
      hcard, ite_true, Multiset.map_map]
    rfl
  simpa only [U.invariantMap_apply, LinearMap.compMultilinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply] using congrArg (fun f ↦ f a) heq

end SurfacePrimary
namespace SurfaceTheoryIdentification
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}

/-- The existing string and divisor laws force the abstract action to equal
the identified surface cup product. No extra compatibility assumption is used. -/
theorem divisorAction_eq_mul (T : SurfaceTheoryIdentification X Omega)
    (U : UnstableDescendantConventions M I) (S : DescendantStringDilatonLaws M I)
    (L : DescendantDivisorLaw M I A) (d : Omega.graded.degree 1)
    (x : SurfaceCohomology X.blowups) : L.divisorAction d x = d.val * x := by
  apply Omega.pairing.toDual.injective
  ext y
  simp only [SymmetricPerfectPairing.toDual_apply]
  rw [L.divisorAction_pairing U S,
    SurfacePrimary.invariant_zero_cubic U T S (Option (Fin 2)) (by decide +kernel)]
  simp only [T.pairing_eq, CommFrobeniusAlgebra.pairing_apply]
  simp only [Fintype.prod_option, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_assoc]
  rfl

end SurfaceTheoryIdentification
end AxiomaticGW
