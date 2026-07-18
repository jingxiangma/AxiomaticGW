/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Frobenius.Constructions
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Finite-labelled multiplication

This file gives a project-level name to mathlib's multilinear product over an
arbitrary finite label type. The accompanying lemmas isolate the relabelling,
disjoint-union, and unit-insertion calculations used by TFT correlators.
-/

@[expose] public section

namespace AxiomaticGW

namespace TFT

variable (R A S : Type*) [CommRing R] [CommRing A] [Algebra R A] [Fintype S]

/-- Multiplication of a finite family in a commutative algebra, viewed as a
multilinear map with one input for every label in `S`. -/
def finiteProduct : MultilinearMap R (fun _ : S ↦ A) A :=
  MultilinearMap.mkPiAlgebra R S A

variable {R A S}

/-- Evaluation of the finite-labelled multilinear product. -/
@[simp]
theorem finiteProduct_apply (a : S → A) : finiteProduct R A S a = ∏ s, a s := rfl

/-- Finite-labelled multiplication is invariant under relabelling. -/
theorem finiteProduct_domDomCongr {T : Type*} [Fintype T] (e : S ≃ T) :
    (finiteProduct R A S).domDomCongr e = finiteProduct R A T := by
  ext a
  simpa only [MultilinearMap.domDomCongr_apply, finiteProduct_apply] using
    (e.prod_comp a)

/-- The product over a disjoint union is the product of the two component
products. -/
theorem finiteProduct_sum_apply {T : Type*} [Fintype T] (a : S ⊕ T → A) :
    finiteProduct R A (S ⊕ T) a =
      finiteProduct R A S (fun s ↦ a (.inl s)) *
        finiteProduct R A T (fun t ↦ a (.inr t)) := by
  simp only [finiteProduct_apply, Fintype.prod_sum_type]

/-- The product over no labels is the algebra unit. -/
theorem finiteProduct_empty_apply (a : Empty → A) :
    finiteProduct R A Empty a = 1 := by
  simp only [finiteProduct_apply, Finset.univ_eq_empty, Finset.prod_empty]

/-- Adjoining a new label whose value is the algebra unit does not change the
finite product. -/
theorem finiteProduct_option_one_apply (a : S → A) :
    finiteProduct R A (Option S) (fun | none => 1 | some s => a s) =
      finiteProduct R A S a := by
  simp only [finiteProduct_apply, Fintype.prod_option, one_mul]

end TFT

end AxiomaticGW
