/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.Tautological
public import AxiomaticGW.GKM.GenusTwoLocalizationVertex
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # The Hodge and cotangent class of a genus-two localization vertex

The character coefficients extend the rational stable-curve cohomology by tensor product.
Integrating the resulting class gives the numerical vertex with the same ordered marks
and flags. The Hodge classes enter as explicit graded classes on the source curves.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoLocalizationClass
open TensorProduct GenusTwoLocalizationVertex GenusTwoVertexHodgeReduction
noncomputable section

variable {C : StableCurveCohomology ℚ}

/-- The two positive Chern classes of a rank-two bundle at each ordered arity.
A geometric application supplies the classes of the Hodge bundle. -/
structure HodgeClasses (C : StableCurveCohomology ℚ) where
  /-- First Chern class in codimension one. -/
  first (n : ℕ) : (C.H 2 (Fin n)).degree 1
  /-- Second Chern class in codimension two. -/
  second (n : ℕ) : (C.H 2 (Fin n)).degree 2

/-- Every ordered genus-two arity is stable. -/
theorem stable (n : ℕ) : StableArity 2 (Fin n) := by
  unfold StableArity
  omega

/-- Rank two has three Chern coefficients, starting with the unit in codimension zero. -/
def HodgeClasses.coefficient (D : HodgeClasses C) (n : ℕ) (i : Fin 3) :
    (C.H 2 (Fin n)).degree i.val :=
  match i with
  | 0 => ⟨1, show (1 : C.H 2 (Fin n)) ∈ (C.H 2 (Fin n)).degree 0 from SetLike.GradedOne.one_mem⟩
  | 1 => D.first n
  | 2 => D.second n

/-- The two Hodge classes times the ordered cotangent monomial on the source curve. -/
def monomial (D : HodgeClasses C) (P : PsiClasses C) (i j : Fin 3) {n : ℕ}
    (powers : Fin n → ℕ) : C.H 2 (Fin n) :=
  (D.coefficient n i : C.H 2 (Fin n)) * (D.coefficient n j : C.H 2 (Fin n)) *
    P.monomial 2 (Fin n) (stable n) powers

/-- Each monomial is homogeneous before the character coefficients are attached. -/
theorem monomial_degree (D : HodgeClasses C) (P : PsiClasses C) (i j : Fin 3) {n : ℕ}
    (powers : Fin n → ℕ) :
    monomial D P i j powers ∈ (C.H 2 (Fin n)).degree (i.val + j.val + ∑ t, powers t) :=
  SetLike.mul_mem_graded
    (SetLike.mul_mem_graded (D.coefficient n i).property (D.coefficient n j).property)
    (P.monomial_degree 2 (Fin n) (stable n) powers)

/-- The rational numerical Hodge functional is defined by integration of the actual monomial. -/
def moment (D : HodgeClasses C) (P : PsiClasses C) (I : StableCurveIntegration C)
    (i j : Fin 3) (p : List ℕ) : ℚ :=
  I.integrate 2 (Fin p.length) (stable _) (monomial D P i j p.get)

/-- The dimension law for this functional follows from the grading and integration. -/
theorem moment_off_degree (D : HodgeClasses C) (P : PsiClasses C) (I : StableCurveIntegration C)
    (i j : Fin 3) (p : List ℕ) (h : p.sum + i.val + j.val ≠ 3 + p.length) :
    moment D P I i j p = 0 := by
  apply I.integrate_of_degree_ne _ _ _ _ _ (monomial_degree D P i j p.get)
  have hs : ∑ t, p.get t = p.sum := by rw [← List.sum_ofFn, List.ofFn_get]
  simp only [hs, StableArity.dimension, Fintype.card_fin]
  omega

variable {K : Type*} [Field K] [CharZero K]

/-- Integration of rational cohomology after extension to the character field. -/
def integrate (I : StableCurveIntegration C) (n : ℕ) :
    K ⊗[ℚ] (C.H 2 (Fin n)) →ₗ[ℚ] K :=
  (TensorProduct.rid ℚ K).toLinearMap.comp ((I.integrate 2 (Fin n) (stable n)).lTensor K)

/-- Ordered exponents on the combined list of marked points and flags. -/
def markedPowers {f : ℕ} (m : List ℕ) (k : Fin f → ℕ) :
    Fin (m.length + f) → ℕ :=
  (m ++ List.ofFn k).get ∘ Fin.cast (by rw [List.length_append, List.length_ofFn])

private theorem integrated_monomial (D : HodgeClasses C) (P : PsiClasses C)
    (I : StableCurveIntegration C) {n : ℕ} (i j : Fin 3) (p : List ℕ) (h : n = p.length) :
    I.integrate 2 (Fin n) (stable n) (monomial D P i j (p.get ∘ Fin.cast h)) =
      moment D P I (min i j) (max i j) p := by
  subst n
  rcases le_total i j with hij | hji
  · rw [min_eq_left hij, max_eq_right hij]
    rfl
  · rw [min_eq_right hji, max_eq_left hji]
    apply congrArg (I.integrate 2 (Fin p.length) (stable _))
    unfold monomial
    rw [mul_comm (D.coefficient p.length i : C.H 2 (Fin p.length)) (D.coefficient p.length j)]
    rfl

/-- The tensor for one pair of Hodge indices and one flag-power profile. -/
def term (D : HodgeClasses C) (P : PsiClasses C) {f : ℕ} (m : List ℕ)
    (u v : K) (flag : Fin f → K) (i j : Fin 3) (k : Fin f → ℕ) :
    K ⊗[ℚ] (C.H 2 (Fin (m.length + f))) :=
  ((-1 : K)^(i.val+j.val) * (u^((1 : ℤ)-i.val) * v^((1 : ℤ)-j.val) *
    ∏ s, (flag s)^(-(k s : ℤ)-1))) ⊗ₜ[ℚ] monomial D P i j (markedPowers m k)

/-- Top-degree part of the vertex before integration. Markings precede incident flags. -/
def topClass (D : HodgeClasses C) (P : PsiClasses C) {f : ℕ} (m : List ℕ)
    (u v : K) (flag : Fin f → K) : K ⊗[ℚ] (C.H 2 (Fin (m.length + f))) :=
  ∑ j : Fin 3, ∑ i : Fin 3, ∑ k ∈ profiles f m i j, term D P m u v flag i j k

/-- Integration of the pre-integration class gives the full rational-function vertex source. -/
theorem integrate_topClass (D : HodgeClasses C) (P : PsiClasses C) (I : StableCurveIntegration C)
    {f : ℕ} (m : List ℕ) (u v : K) (flag : Fin f → K) :
    integrate I _ (topClass D P m u v flag) =
      source (fun i j _ ↦ moment D P I i j) m u v flag := by
  unfold topClass source
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [term, integrate, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul, markedPowers, integrated_monomial, Rat.smul_def,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one]
  ac_rfl

/-- Retain every flag exponent from zero up to the dimension, independently at each flag. -/
def flagBox (n f : ℕ) : Finset (Fin f → ℕ) :=
  Fintype.piFinset fun _ ↦ Finset.range (3 + n + f + 1)

private theorem profiles_subset (m : List ℕ) (f : ℕ) (i j : Fin 3) :
    profiles f m i j ⊆ flagBox m.length f := by
  intro k hk
  have hd := (mem_profiles m i j k).mp hk
  apply Fintype.mem_piFinset.mpr
  intro t
  have ht : k t ≤ ∑ s, k s := Finset.single_le_sum (fun s _ ↦ Nat.zero_le (k s)) (Finset.mem_univ t)
  exact Finset.mem_range.mpr (by omega)

/-- The finite expansion includes lower-degree terms and mixed terms above the dimension. -/
def expansion (D : HodgeClasses C) (P : PsiClasses C) {f : ℕ} (m : List ℕ)
    (u v : K) (flag : Fin f → K) : K ⊗[ℚ] (C.H 2 (Fin (m.length + f))) :=
  ∑ j : Fin 3, ∑ i : Fin 3, ∑ k ∈ flagBox m.length f, term D P m u v flag i j k

/-- Integrating the full finite expansion automatically selects the top-degree flag profiles. -/
theorem integrate_expansion (D : HodgeClasses C) (P : PsiClasses C) (I : StableCurveIntegration C)
    {f : ℕ} (m : List ℕ) (u v : K) (flag : Fin f → K) :
    integrate I _ (expansion D P m u v flag) =
      source (fun i j _ ↦ moment D P I i j) m u v flag := by
  rw [← integrate_topClass, expansion, topClass]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  symm
  apply Finset.sum_subset (profiles_subset m f i j)
  intro k _ hk
  rw [mem_profiles] at hk
  have hd : (m ++ List.ofFn k).sum + (min i j).val + (max i j).val ≠
      3 + (m ++ List.ofFn k).length := by
    simp only [List.sum_append, List.sum_ofFn, List.length_append, List.length_ofFn]
    rcases le_total i j with hij | hji
    · rw [min_eq_left hij, max_eq_right hij]
      omega
    · rw [min_eq_right hji, max_eq_left hji]
      omega
  simp only [term, integrate, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul, markedPowers, integrated_monomial, moment_off_degree D P I _ _ _ hd,
    zero_smul]

/-- The full pre-integration expansion is determined numerically by eight rational moments
under the Hodge string, dilaton and relabeling laws. -/
theorem integrate_eq_reduced (D : HodgeClasses C) (P : PsiClasses C) (I : StableCurveIntegration C)
    (seed : ↥seeds → ℚ)
    (laws : ∀ (i j : Fin 3), i ≤ j → Recurrences i j (moment D P I i j))
    (hseed : ∀ (i j : Fin 3), i ≤ j → ∀ p (hk : ((i : ℕ), (j : ℕ), p) ∈ seeds),
      seed ⟨_, hk⟩ = moment D P I i j p) {f : ℕ} (m : List ℕ) (u v : K) (flag : Fin f → K) :
    integrate I _ (expansion D P m u v flag) = reduced seed m u v flag :=
  (integrate_expansion D P I m u v flag).trans
    (reduced_eq_source seed (fun i j _ ↦ moment D P I i j) laws hseed m u v flag).symm

end
end AxiomaticGW.GKM.GenusTwoLocalizationClass
