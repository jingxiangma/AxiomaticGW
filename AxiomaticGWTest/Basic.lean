/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW

/-!
# API regression tests

These examples check that the public import and local-instance interfaces work
as intended. They are deliberately kept outside the production library.
-/

namespace AxiomaticGWTest

open AxiomaticGW TensorProduct

namespace Contraction

/-- Scalar contraction commutes with relabelling the inputs that remain after
the two node inputs are contracted. -/
example {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Module.Free R V] [Module.Finite R V]
    (P : AxiomaticGW.SymmetricPerfectPairing R V) {S T : Type*}
    (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) R) (e : S ≃ T) :
    (P.selfContract f).domDomCongr e =
      P.selfContract
        (f.domDomCongr (Equiv.sumCongr e (Equiv.refl (Fin 2)))) := by
  exact P.selfContract_domDomCongr f e

/-- Target-valued contraction uses the same relabelling convention. -/
example {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Module.Free R V] [Module.Finite R V] [AddCommGroup W] [Module R W]
    (P : AxiomaticGW.SymmetricPerfectPairing R V) {S T : Type*}
    (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) W) (e : S ≃ T) :
    (P.selfContractTarget f).domDomCongr e =
      P.selfContractTarget
        (f.domDomCongr (Equiv.sumCongr e (Equiv.refl (Fin 2)))) := by
  exact P.selfContractTarget_domDomCongr f e

end Contraction

namespace CommFrobeniusAlgebra

/-- The canonical coalgebra can be installed locally without choosing a global
Frobenius structure. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (a : A) :
    letI : Coalgebra R A := F.toCoalgebra
    Coalgebra.counit (R := R) (A := A) a = F.counit a := by
  rfl

/-- The cocommutativity proof is compatible with the locally installed coalgebra. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (a : A) :
    TensorProduct.comm R A A (F.comul a) = F.comul a := by
  letI : Coalgebra R A := F.toCoalgebra
  letI : Coalgebra.IsCocomm R A := F.toIsCocomm
  exact Coalgebra.comm_comul R a

/-- The rank-two example remains available through the project entry point. -/
example (R : Type*) [CommRing R] :
    (AxiomaticGW.CommFrobeniusAlgebra.productAlgebra R).handleElement = 1 := by
  simp only [CommFrobeniusAlgebra.productAlgebra_handleElement]

/-- The bundled two-dimensional TFT exposes the nonseparating gluing law. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (g : ℕ) :
    F.pairing.selfContract (F.correlator g (Fin 1 ⊕ Fin 2)) =
      F.correlator (g + 1) (Fin 1) := by
  exact (F.toTwoDimensionalTFT.nonseparating g (Fin 1))

/-- The bundled two-dimensional TFT exposes the separating gluing law. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (g₁ g₂ : ℕ) :
    F.pairing.pairContract (F.correlator g₁ (Option (Fin 1)))
        (F.correlator g₂ (Option (Fin 1))) =
      F.correlator (g₁ + g₂) (Fin 1 ⊕ Fin 1) := by
  exact (F.toTwoDimensionalTFT.separating g₁ g₂ (Fin 1) (Fin 1))

/-- The base-ring example computes every genus and finite arity. -/
example (R : Type*) [CommRing R] (g : ℕ) (a : Fin 3 → R) :
    (AxiomaticGW.CommFrobeniusAlgebra.baseRing R).correlator g (Fin 3) a =
      ∏ i, a i := by
  simp only [CommFrobeniusAlgebra.correlator_apply,
    CommFrobeniusAlgebra.baseRing_handleElement, one_pow, mul_one,
    CommFrobeniusAlgebra.baseRing_counit_apply]

/-- A correlator with no marked inputs is the closed-surface partition
function. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (g : ℕ) (a : Empty → A) :
    F.correlator g Empty a = F.counit (F.handleElement ^ g) := by
  exact F.correlator_empty_apply g a

/-- Inserting the algebra unit at a new marking preserves the correlator. -/
example {R A S : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A] [Fintype S]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (g : ℕ) (a : S → A) :
    F.correlator g (Option S) (fun | none => 1 | some s => a s) =
      F.correlator g S a := by
  exact F.correlator_option_one_apply g a

/-- Restriction to stable arities preserves the underlying correlator. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) :
    F.toTopologicalCohFT.omega 0 (Fin 3) AxiomaticGW.StableArity.zero_fin_three =
      F.correlator 0 (Fin 3) := by
  rfl

/-- The three-point product extracted from the forward theory is the original
algebra multiplication. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (x y : A) :
    F.toTwoDimensionalTFT.product x y = x * y := by
  exact F.toTwoDimensionalTFT_product x y

/-- The canonical public name for the curried three-point correlator is
`threePointFunction`. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (x y z : A) :
    F.toTwoDimensionalTFT.threePointFunction x y z =
      F.correlator 0 (Fin 3) (Fin.cons x (Fin.cons y fun _ ↦ z)) := by
  exact F.toTwoDimensionalTFT.threePointFunction_apply x y z

end CommFrobeniusAlgebra

namespace FullCohFT

/-- The constant stable-curve system is concentrated in codimension zero. -/
example (r : ℚ) : r ∈ AxiomaticGW.constantDegree ℚ 0 := by
  simp only [AxiomaticGW.constantDegree, ↓reduceIte, Submodule.mem_top]

/-- The forget/nonseparating transport cycles the forgotten marking past the
two ordered node markings and fixes every original marking. -/
example (S : Type) (s : S) :
    AxiomaticGW.forgetNonseparatingEquiv S none = some none ∧
      AxiomaticGW.forgetNonseparatingEquiv S (some none) =
        some (some none) ∧
      AxiomaticGW.forgetNonseparatingEquiv S (some (some none)) = none ∧
      AxiomaticGW.forgetNonseparatingEquiv S (some (some (some s))) =
        some (some (some s)) := by
  simp only [AxiomaticGW.forgetNonseparatingEquiv, Equiv.coe_fn_mk, and_self]

/-- Forgetting after nonseparating gluing exposes the required transport of
the forgotten marking and node labels. -/
example {R : Type*} [CommRing R] [Algebra ℚ R]
    (C : AxiomaticGW.StableCurveCohomology R) (g : ℕ) (S : Type)
    [Fintype S] (h : AxiomaticGW.StableArity (g + 1) S) :
    (C.forget g (Option (Option S))
        (AxiomaticGW.StableArity.double_option_iff.mpr h)).comp
        (C.nonseparating g S h) =
      (C.rename g (Option (Option (Option S))) (Option (Option (Option S)))
        (AxiomaticGW.StableArity.double_option_iff.mpr
          (AxiomaticGW.StableArity.option h))
        (AxiomaticGW.StableArity.option
          (AxiomaticGW.StableArity.double_option_iff.mpr h))
        (AxiomaticGW.forgetNonseparatingEquiv S)).toAlgHom.comp
          ((C.nonseparating g (Option S) (AxiomaticGW.StableArity.option h)).comp
            (C.forget (g + 1) S h)) := by
  exact C.forget_nonseparating g S h

/-- Forgetting on the left component of a separating boundary transports the
left node and forgotten marking in the tensor target. -/
example {R : Type*} [CommRing R] [Algebra ℚ R]
    (C : AxiomaticGW.StableCurveCohomology R) (g₁ g₂ : ℕ)
    (S T : Type) [Fintype S] [Fintype T]
    (h₁ : AxiomaticGW.StableArity g₁ (Option S))
    (h₂ : AxiomaticGW.StableArity g₂ (Option T)) :
    (Algebra.TensorProduct.map
      (C.forget g₁ (Option S) h₁)
      (AlgHom.id R (C.H g₂ (Option T)))).comp
        (C.separating g₁ g₂ S T h₁ h₂) =
      (Algebra.TensorProduct.map
        (C.rename g₁ (Option (Option S)) (Option (Option S))
          (AxiomaticGW.StableArity.option h₁)
          (AxiomaticGW.StableArity.option h₁)
          (AxiomaticGW.swapDoubleOption S)).toAlgHom
        (AlgHom.id R (C.H g₂ (Option T)))).comp
          ((C.separating g₁ g₂ (Option S) T
            (AxiomaticGW.StableArity.option h₁) h₂).comp
            ((C.rename (g₁ + g₂) (Option (S ⊕ T)) (Option S ⊕ T)
              (AxiomaticGW.StableArity.option
                (AxiomaticGW.StableArity.separating h₁ h₂))
              (AxiomaticGW.StableArity.separating
                (AxiomaticGW.StableArity.option h₁) h₂)
              (AxiomaticGW.optionSumEquivLeft S T)).toAlgHom.comp
                (C.forget (g₁ + g₂) (S ⊕ T)
                  (AxiomaticGW.StableArity.separating h₁ h₂)))) := by
  exact C.forget_separating_left g₁ g₂ S T h₁ h₂

/-- The abstract stable-curve target enforces its geometric top degree. -/
example {R : Type*} [CommRing R] [Algebra ℚ R]
    (C : AxiomaticGW.StableCurveCohomology R) (g : ℕ) (S : Type)
    [Fintype S] (h : AxiomaticGW.StableArity g S) (d : ℕ)
    (x : C.H g S) (hx : x ∈ (C.H g S).degree d)
    (hd : AxiomaticGW.StableArity.dimension g S < d) : x = 0 := by
  exact C.eq_zero_of_dimension_lt g S h d x hx hd

/-- Forgetful pushforward kills degree zero and transports kappa classes under
relabelling. -/
example {R : Type*} [CommRing R] [Algebra ℚ R]
    {C : AxiomaticGW.StableCurveCohomology R}
    (P : AxiomaticGW.PsiClasses C) (I : AxiomaticGW.StableCurveIntegration C)
    (F : AxiomaticGW.ForgetfulPushforward C I) (g : ℕ) (S T : Type)
    [Fintype S] [Fintype T] (hS : AxiomaticGW.StableArity g S)
    (hT : AxiomaticGW.StableArity g T) (e : S ≃ T) (m : ℕ)
    (x : C.H g (Option S)) (hx : x ∈ (C.H g (Option S)).degree 0) :
    F.push g S hS x = 0 ∧
      C.rename g S T hS hT e (P.kappa F g S hS m) =
        P.kappa F g T hT m ∧
      P.kappa F g S hS m ∈ (C.H g S).degree m := by
  exact ⟨F.push_eq_zero_of_degree_zero g S hS x hx,
    P.kappa_rename F g S T hS hT e m, P.kappa_degree F g S hS m⟩

/-- Scalar topological correlators become the classes of the full CohFT over
the constant target. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) :
    T.toConstantCohFT.omega 0 (Fin 3) AxiomaticGW.StableArity.zero_fin_three =
      T.omega 0 (Fin 3) AxiomaticGW.StableArity.zero_fin_three := by
  rfl

/-- Relabelling is exposed by the converted full CohFT. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (e : Fin 3 ≃ Fin 3) :
    ((AxiomaticGW.constantStableCurveCohomology ℚ).rename 0
      (Fin 3) (Fin 3) AxiomaticGW.StableArity.zero_fin_three
      AxiomaticGW.StableArity.zero_fin_three e).toLinearMap.compMultilinearMap
        ((T.toConstantCohFT.omega 0 (Fin 3)
          AxiomaticGW.StableArity.zero_fin_three).domDomCongr e) =
      T.toConstantCohFT.omega 0 (Fin 3)
        AxiomaticGW.StableArity.zero_fin_three := by
  exact T.toConstantCohFT.relabel 0 (Fin 3) (Fin 3)
    AxiomaticGW.StableArity.zero_fin_three
    AxiomaticGW.StableArity.zero_fin_three e

/-- The converted full CohFT exposes nonseparating gluing with a
cohomology-valued target. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g : ℕ) (S : Type) [Fintype S]
    (h : AxiomaticGW.StableArity (g + 1) S) :
    T.pairing.selfContractTarget
        ((T.toConstantCohFT.omega g (Option (Option S))
          (AxiomaticGW.StableArity.double_option_iff.mpr h)).domDomCongr
            (AxiomaticGW.doubleOptionEquiv S)) =
      LinearMap.compMultilinearMap
        ((AxiomaticGW.constantStableCurveCohomology ℚ).nonseparating g S h).toLinearMap
        (T.toConstantCohFT.omega (g + 1) S h) := by
  exact T.toConstantCohFT.nonseparating g S h

/-- Flat-unit insertion survives conversion to the full CohFT. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g : ℕ) (S : Type) [Fintype S]
    (h : AxiomaticGW.StableArity g S) (a : S → V) :
    T.toConstantCohFT.omega g (Option S) (AxiomaticGW.StableArity.option h)
        (fun | none => T.unit | some s => a s) =
      (AxiomaticGW.constantStableCurveCohomology ℚ).forget g S h
        (T.toConstantCohFT.omega g S h a) := by
  exact T.toConstantCohFT.unit_insert g S h a

/-- Separating gluing survives conversion to the tensor-valued full CohFT. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g₁ g₂ : ℕ)
    (S U : Type) [Fintype S] [Fintype U]
    (h₁ : AxiomaticGW.StableArity g₁ (Option S))
    (h₂ : AxiomaticGW.StableArity g₂ (Option U)) :
    T.pairing.pairContractTarget
        (T.toConstantCohFT.omega g₁ (Option S) h₁)
        (T.toConstantCohFT.omega g₂ (Option U) h₂) =
      LinearMap.compMultilinearMap
        ((AxiomaticGW.constantStableCurveCohomology ℚ).separating
          g₁ g₂ S U h₁ h₂).toLinearMap
        (T.toConstantCohFT.omega (g₁ + g₂) (S ⊕ U)
          (AxiomaticGW.StableArity.separating h₁ h₂)) := by
  exact T.toConstantCohFT.separating g₁ g₂ S U h₁ h₂

/-- Conversion to the full constant model and back preserves all scalar
correlators. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g : ℕ) (S : Type) [Fintype S]
    (h : AxiomaticGW.StableArity g S) :
    T.toConstantCohFT.toTopologicalCohFT.omega g S h = T.omega g S h := by
  simp only [AxiomaticGW.TopologicalCohFT.toConstantCohFT_toTopologicalCohFT_omega]

/-- The generic degree-zero construction specializes to the original
topological theory on the constant target. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g : ℕ) (S : Type) [Fintype S]
    (h : AxiomaticGW.StableArity g S) :
    (T.toConstantCohFT.topologicalPart
      (AxiomaticGW.constantStableCurveCohomology.connectedDegreeZero ℚ)).omega
        g S h = T.omega g S h := by
  simp only [AxiomaticGW.TopologicalCohFT.toConstantCohFT_topologicalPart_omega]

/-- The genus-zero product extracted from a topological CohFT is associative. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (x y z : V) :
    let T₀ := T.toConstantCohFT.toGenusZeroCohFT
    let G := AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ
    T₀.product G (T₀.product G x y) z = T₀.product G x (T₀.product G y z) := by
  exact T.toConstantCohFT.toGenusZeroCohFT.product_assoc
    (AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ) x y z

/-- Frobenius reconstruction agrees with every stable correlator, in every
genus and finite label type. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g : ℕ) (S : Type) [Fintype S]
    (h : AxiomaticGW.StableArity g S) :
    ((T.toCommFrobeniusAlgebra.toTopologicalCohFT.omega g S h).compLinearMap
      (fun _ ↦ (AxiomaticGW.GenusZeroCohFT.FrobeniusCarrier.toStateSpace
        T.toConstantCohFT.toGenusZeroCohFT
        (AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ)).symm.toLinearMap)) =
      T.omega g S h := by
  exact T.classification g S h

/-- The first tautological extension is usable through the public import: in
the constant target, a zero-power three-point ancestor is the original
topological correlator. -/
example {V : Type} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (a : Fin 3 → V) :
    T.toConstantCohFT.ancestor
        (AxiomaticGW.constantStableCurveCohomology.psiClasses ℚ)
        (AxiomaticGW.constantStableCurveCohomology.integration ℚ)
        0 (Fin 3) AxiomaticGW.StableArity.zero_fin_three (fun _ ↦ 0) a =
      T.omega 0 (Fin 3) AxiomaticGW.StableArity.zero_fin_three a := by
  exact T.toConstantCohFT_ancestor_zero_three a

end FullCohFT

namespace GromovWittenTheory

/-- Descendant cotangent powers participate in the virtual-dimension
equation and can compensate a negative primary expected degree. -/
example : AxiomaticGW.GWOutputDegree 1 0 (0 + 3) 0 2 := by
  norm_num [AxiomaticGW.GWOutputDegree]

/-- Descendants, ancestors, and their residual share the corrected total
degree. -/
example {R V B : Type} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : AxiomaticGW.EffectiveCurveMonoid B}
    {C : AxiomaticGW.StableCurveCohomology R}
    {Omega : AxiomaticGW.GromovWittenTheory R V B D C}
    (P : AxiomaticGW.PsiClasses C)
    (M : AxiomaticGW.StableMapDescendants Omega)
    (X : AxiomaticGW.DescendantAncestorComparison P M)
    (g : ℕ) (S : Type) [Fintype S] (h : AxiomaticGW.StableArity g S)
    (beta : B) (k p : S → ℕ) (a : S → V) (q : ℕ)
    (ha : ∀ s, a s ∈ Omega.graded.degree (p s))
    (hq : AxiomaticGW.GWOutputDegree Omega.graded.dimension g
      ((∑ s, p s) + ∑ s, k s) q (Omega.c1Degree beta)) :
    M.descendantClass g S h beta k a ∈ (C.H g S).degree q ∧
      Omega.ancestorClass P g S h beta k a ∈ (C.H g S).degree q ∧
      X.boundaryCorrection g S h beta k a ∈ (C.H g S).degree q := by
  exact ⟨M.descendant_total_degree g S h beta k p a q ha hq,
    Omega.ancestorClass_total_degree P g S h beta k p a q ha hq,
    X.boundaryCorrection_degree g S h beta k p a q ha hq⟩

/-- The natural-number model exposes exactly the additive curve-class
splittings used by coefficientwise gluing. -/
example : (1, 2) ∈ (AxiomaticGW.EffectiveCurveMonoid.nat).splittings 3 := by
  simp only [AxiomaticGW.EffectiveCurveMonoid.mem_splittings, Nat.reduceAdd]

/-- The beta-zero reference theory recovers its underlying CohFT class. -/
example (g : ℕ) (S : Type) [Fintype S] (h : AxiomaticGW.StableArity g S) :
    (AxiomaticGW.constantGromovWittenTheory.theory ℚ
      AxiomaticGW.EffectiveCurveMonoid.nat).omega g S h 0 =
      (AxiomaticGW.constantGromovWittenTheory.cohft ℚ).omega g S h := by
  exact AxiomaticGW.constantGromovWittenTheory.theory_omega_zero ℚ
    AxiomaticGW.EffectiveCurveMonoid.nat g S h

/-- Small quantum associativity is derived directly from coefficientwise
gluing and WDVV. -/
example (beta : ℕ) (x y z : ℚ) :
    (∑ split ∈ AxiomaticGW.EffectiveCurveMonoid.nat.splittings beta,
      (AxiomaticGW.constantGromovWittenTheory.theory ℚ
        AxiomaticGW.EffectiveCurveMonoid.nat).smallQuantumProductCoefficient
          (AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ)
          split.2
          ((AxiomaticGW.constantGromovWittenTheory.theory ℚ
            AxiomaticGW.EffectiveCurveMonoid.nat).smallQuantumProductCoefficient
              (AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ)
              split.1 x y) z) =
      ∑ split ∈ AxiomaticGW.EffectiveCurveMonoid.nat.splittings beta,
        (AxiomaticGW.constantGromovWittenTheory.theory ℚ
          AxiomaticGW.EffectiveCurveMonoid.nat).smallQuantumProductCoefficient
            (AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ)
            split.2 x
            ((AxiomaticGW.constantGromovWittenTheory.theory ℚ
              AxiomaticGW.EffectiveCurveMonoid.nat).smallQuantumProductCoefficient
                (AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ)
                split.1 y z) := by
  exact (AxiomaticGW.constantGromovWittenTheory.theory ℚ
    AxiomaticGW.EffectiveCurveMonoid.nat).smallQuantumProductCoefficient_assoc
      (AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ)
      beta x y z

/-- The big quantum product specializes to the small quantum product at zero primary
background. -/
example (x y : ℚ) (beta : ℕ) :
    (AxiomaticGW.constantGromovWittenTheory.theory ℚ
      AxiomaticGW.EffectiveCurveMonoid.nat).bigQuantumProduct
        (AxiomaticGW.constantStableCurveCohomology.integration ℚ)
        (Module.Basis.singleton Unit ℚ) x y 0 beta =
      (AxiomaticGW.constantGromovWittenTheory.theory ℚ
        AxiomaticGW.EffectiveCurveMonoid.nat).smallQuantumProductCoefficient
          (AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ)
          beta x y := by
  apply (AxiomaticGW.constantGromovWittenTheory.theory ℚ
    AxiomaticGW.EffectiveCurveMonoid.nat).bigQuantumProduct_zero
      (AxiomaticGW.constantStableCurveCohomology.integration ℚ)
      (AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ)
      (Module.Basis.singleton Unit ℚ)
  change AxiomaticGW.constantStableCurveCohomology.integrate ℚ 0 (Fin 3) =
    LinearMap.id
  simp only [AxiomaticGW.constantStableCurveCohomology.integrate_zero_fin_three]

/-- Relabelling the distinguished insertions makes the big quantum product
commutative at every primary background. -/
example (x y : ℚ) :
    (AxiomaticGW.constantGromovWittenTheory.theory ℚ
      AxiomaticGW.EffectiveCurveMonoid.nat).bigQuantumProduct
        (AxiomaticGW.constantStableCurveCohomology.integration ℚ)
        (Module.Basis.singleton Unit ℚ) x y =
      (AxiomaticGW.constantGromovWittenTheory.theory ℚ
        AxiomaticGW.EffectiveCurveMonoid.nat).bigQuantumProduct
          (AxiomaticGW.constantStableCurveCohomology.integration ℚ)
          (Module.Basis.singleton Unit ℚ) y x := by
  exact (AxiomaticGW.constantGromovWittenTheory.theory ℚ
    AxiomaticGW.EffectiveCurveMonoid.nat).bigQuantumProduct_comm
      (AxiomaticGW.constantStableCurveCohomology.integration ℚ)
      (Module.Basis.singleton Unit ℚ) x y

end GromovWittenTheory

namespace StableGraphs

/-- A loop contributes two branches to valence and one to the first Betti
number. -/
def loopGraph : AxiomaticGW.StableGraph (Fin 1) where
  Vertex := Unit
  Edge := Unit
  legVertex := fun _ ↦ ()
  endpoint := fun _ _ ↦ ()
  genus := fun _ ↦ 0
  connected := by
    intro v w
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    exact Relation.ReflTransGen.refl
  stable := by
    simp only [mul_zero, Fintype.card_subtype_true, Fintype.card_unique,
      zero_add, Fintype.card_prod, Fintype.card_fin, one_mul, Nat.reduceAdd,
      Std.le_refl, implies_true]

example : loopGraph.totalGenus = 1 := by
  simp only [AxiomaticGW.StableGraph.totalGenus, loopGraph,
    Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_const_zero,
    AxiomaticGW.StableGraph.firstBetti, Fintype.card_unique, Nat.reduceAdd,
    Nat.add_one_sub_one, zero_add]

example : AxiomaticGW.StableArity
    (loopGraph.genus ()) (loopGraph.VertexLabel ()) :=
  loopGraph.vertex_stable ()

/-- Complete contraction orders are permutation-equivalent, including for a
graph with two distinct loop edges. -/
def twoLoopGraph : AxiomaticGW.StableGraph Empty where
  Vertex := Unit
  Edge := Bool
  legVertex := fun s ↦ nomatch s
  endpoint := fun _ _ ↦ ()
  genus := fun _ ↦ 0
  connected := by
    intro v w
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    exact Relation.ReflTransGen.refl
  stable := by
    simp only [mul_zero, Fintype.card_eq_zero, add_zero,
      Fintype.card_subtype_true, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_fin, Nat.reduceMul, zero_add, Nat.reduceLeDiff, implies_true]

example (o₁ o₂ : twoLoopGraph.ContractionOrder) :
    o₁.edges.Perm o₂.edges :=
  twoLoopGraph.contractionOrder_perm o₁ o₂

/-- The constant stable-curve target supplies a concrete order-independent
graph pullback. -/
example (o₁ o₂ : twoLoopGraph.ContractionOrder) :
    (AxiomaticGW.constantStableCurveCohomology.stableGraphPullbacks ℚ).orderedPullback
        twoLoopGraph o₁ =
      (AxiomaticGW.constantStableCurveCohomology.stableGraphPullbacks ℚ).orderedPullback
        twoLoopGraph o₂ :=
  (AxiomaticGW.constantStableCurveCohomology.stableGraphPullbacks ℚ).orderedPullback_eq
    twoLoopGraph o₁ o₂

end StableGraphs

namespace HigherAndUnstableExtensions

/-- Genus-zero WDVV at arbitrary primary background is consumed as a scalar
boundary identity and yields a state-valued associativity coefficient by
metric nondegeneracy. -/
example {R V B : Type} {ι : Type} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : AxiomaticGW.EffectiveCurveMonoid B}
    {C : AxiomaticGW.StableCurveCohomology R}
    (Omega : AxiomaticGW.GromovWittenTheory R V B D C)
    (I : AxiomaticGW.StableCurveIntegration C) (b : Module.Basis ι R V)
    (H : Omega.GenusZeroWDVV I b)
    (n : ι →₀ ℕ) (beta : B) (x y z : V) :
    Omega.bigQuantumProductAssocLeftCoefficient I b n beta x y z =
      Omega.bigQuantumProductAssocRightCoefficient I b n beta x y z :=
  Omega.bigQuantumProductCoefficient_assoc I b H n beta x y z

/-- The global string equation really combines the stable law with the
exceptional unstable convention. -/
example {R V B : Type} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : AxiomaticGW.EffectiveCurveMonoid B}
    {C : AxiomaticGW.StableCurveCohomology R}
    {Omega : AxiomaticGW.GromovWittenTheory R V B D C}
    {M : AxiomaticGW.StableMapDescendants Omega}
    {I : AxiomaticGW.StableCurveIntegration C}
    (U : AxiomaticGW.UnstableDescendantConventions M I)
    (L : AxiomaticGW.DescendantStringDilatonLaws M I)
    (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (beta : B) (k : S → ℕ) (a : S → V) :
    U.invariant g (Option S) beta
        (fun | none => 0 | some s => k s)
        (fun | none => Omega.unit | some s => a s) =
      ∑ s, if k s = 0 then 0 else
        U.invariant g S beta (AxiomaticGW.lowerPower k s) a :=
  U.global_string L g S beta k a

/-- Positive-tail support excludes the zero class on the tail component. -/
example : (1, 2) ∈
    AxiomaticGW.EffectiveCurveMonoid.nat.positiveTailSplittings 3 := by
  simp only [AxiomaticGW.EffectiveCurveMonoid.mem_positiveTailSplittings,
    Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_self]

end HigherAndUnstableExtensions

namespace PointTarget

/-- Point descendants recover the normalized zero-dimensional intersection
on `Mbar(0,3)`. -/
example :
    AxiomaticGW.PointTarget.intersectionNumber
        (AxiomaticGW.constantStableCurveCohomology.psiClasses ℚ)
        (AxiomaticGW.constantStableCurveCohomology.integration ℚ)
        0 (Fin 3) (fun _ ↦ 0) = 1 := by
  apply AxiomaticGW.PointTarget.intersectionNumber_zero_three
  rfl

/-- The dimension rule kills a degree-zero integrand on `Mbar(0,4)`. -/
example :
    AxiomaticGW.PointTarget.intersectionNumber
        (AxiomaticGW.constantStableCurveCohomology.psiClasses ℚ)
        (AxiomaticGW.constantStableCurveCohomology.integration ℚ)
        0 (Fin 4) (fun _ ↦ 0) = 0 := by
  apply AxiomaticGW.PointTarget.intersectionNumber_eq_zero_of_degree_ne
    (h := by
      simp only [AxiomaticGW.StableArity, mul_zero, Fintype.card_fin,
        zero_add, Nat.reduceLeDiff])
  simp only [Finset.sum_const_zero, AxiomaticGW.StableArity.dimension,
    mul_zero, Fintype.card_fin, zero_add, Nat.reduceSub, ne_eq, zero_ne_one,
    not_false_eq_true]

/-- The DVV normalization uses `(2 * 1 + 1)!! = 3`. -/
example : AxiomaticGW.PointTarget.oddDoubleFactorial 1 = 3 := by
  norm_num [AxiomaticGW.PointTarget.oddDoubleFactorial,
    Finset.prod_range_succ]

end PointTarget

namespace CompletedCoefficients

/-- Novikov monomials retain the full curve class under multiplication. -/
example :
    AxiomaticGW.NovikovSeries.monomial
        AxiomaticGW.EffectiveCurveMonoid.nat 2 (3 : ℚ) *
      AxiomaticGW.NovikovSeries.monomial
        AxiomaticGW.EffectiveCurveMonoid.nat 5 (7 : ℚ) =
    AxiomaticGW.NovikovSeries.monomial
      AxiomaticGW.EffectiveCurveMonoid.nat 7 (21 : ℚ) := by
  norm_num

/-- The Laurent total free energy exposes the original genus coefficient. -/
example (F : AxiomaticGW.GenusPotential ℚ) (g : ℕ) :
    (AxiomaticGW.totalFreeEnergy F).coeff ((g : ℤ) - 1) = F g := by
  simp only [AxiomaticGW.totalFreeEnergy_coeff]

/-- Formal partial derivatives in distinct variables commute. -/
example (f : MvPowerSeries (Fin 2) ℚ) :
    AxiomaticGW.MvPowerSeries.pderiv 0
        (AxiomaticGW.MvPowerSeries.pderiv 1 f) =
      AxiomaticGW.MvPowerSeries.pderiv 1
        (AxiomaticGW.MvPowerSeries.pderiv 0 f) := by
  exact AxiomaticGW.MvPowerSeries.pderiv_comm (by decide) f

/-- Formal partial differentiation obeys the product rule on completed
multivariable power series. -/
example (f g : MvPowerSeries (Fin 2) ℚ) :
    AxiomaticGW.MvPowerSeries.pderiv 0 (f * g) =
      AxiomaticGW.MvPowerSeries.pderiv 0 f * g +
        f * AxiomaticGW.MvPowerSeries.pderiv 0 g := by
  exact AxiomaticGW.MvPowerSeries.pderiv_mul 0 f g

/-- A repeated variable contributes its factorial to a potential profile. -/
example :
    AxiomaticGW.profileFactorial (Finsupp.single () 2) = 2 := by
  norm_num [AxiomaticGW.profileFactorial]

end CompletedCoefficients

end AxiomaticGWTest
