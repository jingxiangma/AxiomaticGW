/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PrimaryReduction

/-!
# Degree-zero primary surface invariants

The genus-zero classical cubic is derived from the existing string equation,
surface grading, unit, and metric. It is not an additional value oracle.
The arguments apply to arbitrary insertion multiplicities and include the
auxiliary zero convention at curve-unstable degree-zero arities.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceBasisLabel

/-- The finite genus-one degree-zero divisor values; other basis states
vanish by dimension. These numbers remain geometric seed obligations. -/
def genusOneZeroValue {X : SurfaceTarget} : SurfaceBasisLabel X → ℚ
  | hyperplane => -1 / 8
  | exceptional _ => -1 / 24
  | unit | point => 0

/-- Without a unit every basis insertion has positive codimension. -/
theorem card_le_sum_codimension {X : SurfaceTarget}
    (m : Multiset (SurfaceBasisLabel X)) (hunit : .unit ∉ m) :
    m.card ≤ (m.map codimension).sum := by
  classical
  rw [← Multiset.map_univ]
  change m.card ≤ ∑ s : m, (s : SurfaceBasisLabel X).codimension
  have h : (∑ _s : m, (1 : ℕ)) ≤ ∑ s : m, (s : SurfaceBasisLabel X).codimension := by
    apply Finset.sum_le_sum
    intro s _
    have hs : (s : SurfaceBasisLabel X) ≠ .unit := by
      intro heq
      exact hunit (heq ▸ Multiset.coe_mem)
    cases h : (s : SurfaceBasisLabel X) <;>
      simp only [h, ne_eq, not_true_eq_false, codimension] at hs ⊢ <;> omega
  simpa only [Finset.sum_const, Finset.card_univ, Multiset.card_coe, smul_eq_mul, mul_one]
    using h

/-- The product of basis states has the sum of their codimensions. -/
theorem prod_value_mem_degree {X : SurfaceTarget} (m : Multiset (SurfaceBasisLabel X)) :
    (m.map value).prod ∈ SurfaceCohomology.degree X.blowups (m.map codimension).sum := by
  induction m using Multiset.induction_on with
  | empty =>
      simpa only [Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero]
        using SurfaceCohomology.one_mem_degree_zero X.blowups
  | cons a m ih =>
      simpa only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
        using SetLike.mul_mem_graded a.value_mem_degree ih

end SurfaceBasisLabel

namespace SurfacePrimary

/-- The classical primary cubic; all other arities have value zero. -/
def classicalValue {X : SurfaceTarget} (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  if m.card = 3 then
    SurfaceCohomology.counit X.blowups (m.map SurfaceBasisLabel.value).prod
  else 0

/-- Only a single divisor insertion survives at genus one and degree zero. -/
def genusOneZeroValue {X : SurfaceTarget} (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  if m.card = 1 then (m.map SurfaceBasisLabel.genusOneZeroValue).sum else 0

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Signed dimension vanishing for the occurrence-based primary invariant. -/
theorem eval_eq_zero_of_dimension_ne (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (g : ℕ) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X))
    (hne : ((m.map SurfaceBasisLabel.codimension).sum : ℤ) ≠
      X.c1Degree beta + (g : ℤ) - 1 + (m.card : ℤ)) : eval U g beta m = 0 := by
  apply U.invariant_eq_zero_of_degree_ne g m beta (fun _ ↦ 0)
    (fun s ↦ (s : SurfaceBasisLabel X).codimension)
    (fun s ↦ (s : SurfaceBasisLabel X).value)
  · intro s
    rw [T.degree_eq]
    exact (s : SurfaceBasisLabel X).value_mem_degree
  · intro heq
    apply hne
    rw [← Multiset.map_univ]
    change ((∑ s : m, (s : SurfaceBasisLabel X).codimension : ℕ) : ℤ) = _
    simp only [Finset.sum_const_zero, Nat.cast_zero, add_zero,
      T.dimension_eq, T.c1Degree_eq, Multiset.card_coe] at heq
    rw [heq]
    unfold GWVirtualDimension
    ring

/-- At degree zero a primary unit contributes only the genus-zero metric
correction; the existing string equation supplies the complete formula. -/
theorem eval_unit_zero (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (S : DescendantStringDilatonLaws M I)
    (g : ℕ) (m : Multiset (SurfaceBasisLabel X)) :
    eval U g 0 (.unit ::ₘ m) =
      if g = 0 then twoPointPairing Omega.pairing m
        (fun s ↦ (s : SurfaceBasisLabel X).value) else 0 := by
  classical
  rw [eval_cons]
  have h := U.global_string S g m 0 (fun _ ↦ 0)
    (fun s ↦ (s : SurfaceBasisLabel X).value)
  simp only [stringCorrection, implies_true, and_self, and_true,
    T.unit_eq, SurfaceBasisLabel.value, ite_true, Finset.sum_const_zero, zero_add] at h ⊢
  convert! h using 1
  congr 1 <;> funext x <;> cases x <;> rfl

/-- The two-point metric correction is the product trace in the surface algebra. -/
theorem twoPointPairing_eq_trace (T : SurfaceTheoryIdentification X Omega)
    (m : Multiset (SurfaceBasisLabel X)) (hm : m.card = 2) :
    twoPointPairing Omega.pairing m (fun s ↦ (s : SurfaceBasisLabel X).value) =
      SurfaceCohomology.counit X.blowups (m.map SurfaceBasisLabel.value).prod := by
  classical
  let e : m ≃ Fin 2 := Fintype.equivFinOfCardEq (by rw [Multiset.card_coe, hm])
  rw [← twoPointPairing_relabel Omega.pairing m (Fin 2) e,
    twoPointPairing_fin_two, T.pairing_eq]
  change SurfaceCohomology.counit X.blowups
    (((e.symm 0 : m) : SurfaceBasisLabel X).value *
      ((e.symm 1 : m) : SurfaceBasisLabel X).value) = _
  congr 1
  rw [← Multiset.map_univ]
  change _ = ∏ s : m, (s : SurfaceBasisLabel X).value
  have hprod := Fintype.prod_equiv e
    (fun s : m ↦ (s : SurfaceBasisLabel X).value)
    (fun i : Fin 2 ↦ ((e.symm i : m) : SurfaceBasisLabel X).value)
    (fun s ↦ by rw [Equiv.symm_apply_apply])
  rw [hprod, Fin.prod_univ_two]

/-- A cubic with no unit has codimension at least three and zero surface trace. -/
theorem classicalValue_eq_zero_of_unit_not_mem
    (m : Multiset (SurfaceBasisLabel X)) (hunit : .unit ∉ m) : classicalValue m = 0 := by
  unfold classicalValue
  split_ifs with hc
  · have hle := SurfaceBasisLabel.card_le_sum_codimension m hunit
    have hgrade := SurfaceBasisLabel.prod_value_mem_degree m
    exact hgrade.2.2 (by omega)
  · rfl

/-- All genus-zero degree-zero primary values follow from string, grading,
and the identified metric, with no independent cubic normalization hypothesis. -/
theorem eval_genus_zero_zero (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (S : DescendantStringDilatonLaws M I)
    (m : Multiset (SurfaceBasisLabel X)) : eval U 0 0 m = classicalValue m := by
  classical
  by_cases hu : .unit ∈ m
  · obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem hu
    rw [eval_unit_zero U T S, if_pos rfl]
    unfold classicalValue
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons,
      SurfaceBasisLabel.value, one_mul]
    by_cases hm : m.card = 2
    · rw [if_pos (by omega)]
      exact twoPointPairing_eq_trace T m hm
    · rw [if_neg (by omega)]
      exact twoPointPairing_eq_zero_of_card_ne_two _ _ _ (by
        simpa only [Multiset.card_coe] using hm)
  · rw [classicalValue_eq_zero_of_unit_not_mem m hu]
    apply eval_eq_zero_of_dimension_ne U T 0 0 m
    have hle := SurfaceBasisLabel.card_le_sum_codimension m hu
    rw [map_zero]
    omega

/-- A singleton multiset is one marking carrying its specified state. -/
theorem eval_singleton (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (b : SurfaceBasisLabel X) :
    eval U g beta {b} = U.invariant g (Fin 1) beta (fun _ ↦ 0) (fun _ ↦ b.value) := by
  classical
  rw [eval, invariant_relabel U g beta _ _
    (Fintype.equivFinOfCardEq (by rw [Multiset.card_coe, Multiset.card_singleton]))]
  congr 1
  funext s
  rw [Multiset.mem_singleton.mp Multiset.coe_mem]

/-- The multiset singleton agrees with the existing list-based query API. -/
theorem eval_singleton_query (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (b : SurfaceBasisLabel X) :
    eval U g beta {b} = (⟨g, beta, [⟨b, 0⟩]⟩ : SurfaceQuery X).eval U := by
  rw [eval_singleton]
  simp only [SurfaceQuery.eval, List.get_eq_getElem, List.getElem_singleton]
  exact (invariant_relabel U g beta _ _
    (finCongr (show ([⟨b, 0⟩] : List (SurfaceInsertion X)).length = 1 from rfl))
    (fun _ ↦ b.value)).symm

/-- A primary divisor at degree zero vanishes when the remaining curve
arity is stable, so neither divisor exception is present. -/
theorem eval_divisor_zero_of_stable (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (g : ℕ) (b : SurfaceBasisLabel X) (hb : b.codimension = 1)
    (m : Multiset (SurfaceBasisLabel X)) (hm : StableArity g m) :
    eval U g 0 (b ::ₘ m) = 0 := by
  classical
  let d : Omega.graded.degree 1 := ⟨b.value, by
    rw [T.degree_eq, ← hb]
    exact b.value_mem_degree⟩
  rw [eval_cons]
  have h := H.global_divisor g m 0 (fun _ ↦ 0)
    (fun s ↦ (s : SurfaceBasisLabel X).value) d
  rw [divisorCorrection_eq_zero_of_stable M I H.genusOneDivisor _ _ _ _ _ _ hm,
    map_zero] at h
  simp only [ite_true, Finset.sum_const_zero, zero_mul, add_zero] at h
  convert! h using 1
  congr 1 <;> funext x <;> cases x <;> rfl

/-- The one-marking genus-one primary values use precisely the existing
hyperplane and exceptional divisor seeds; unit and point values vanish by degree. -/
theorem eval_genus_one_singleton (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (b : SurfaceBasisLabel X) : eval U 1 0 {b} = b.genusOneZeroValue := by
  cases b with
  | unit =>
      apply eval_eq_zero_of_dimension_ne U T 1 0 {.unit}
      norm_num only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_singleton,
        SurfaceBasisLabel.codimension, map_zero]
  | point =>
      apply eval_eq_zero_of_dimension_ne U T 1 0 {.point}
      norm_num only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_singleton,
        SurfaceBasisLabel.codimension, map_zero]
  | hyperplane =>
      rw [eval_singleton_query]
      exact hH
  | exceptional i =>
      rw [eval_singleton_query]
      exact hE i

/-- In genus one, arbitrary degree-zero primary multiplicities reduce to
the finite divisor seeds. The empty unstable convention is included explicitly. -/
theorem eval_genus_one_zero (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (m : Multiset (SurfaceBasisLabel X)) : eval U 1 0 m = genusOneZeroValue m := by
  classical
  unfold genusOneZeroValue
  by_cases hn : m.card = 1
  · rw [if_pos hn]
    obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp hn
    rw [Multiset.map_singleton, Multiset.sum_singleton]
    exact eval_genus_one_singleton U T hH hE b
  rw [if_neg hn]
  by_cases h0 : m.card = 0
  · exact U.invariant_zero_of_unstable 1 m (by
      simp only [StableArity, Multiset.card_coe, h0]
      omega) _ _
  by_cases hu : .unit ∈ m
  · obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem hu
    rw [eval_unit_zero U T S, if_neg Nat.one_ne_zero]
  by_cases hd : ∃ b ∈ m, b.codimension = 1
  · obtain ⟨b, hb, hd⟩ := hd
    obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem hb
    exact eval_divisor_zero_of_stable U T H 1 b hd m (by
      simp only [StableArity, Multiset.card_coe]
      simp only [Multiset.card_cons] at hn
      omega)
  have hp : ∀ b ∈ m, b = .point := by
    intro b hb
    cases b with
    | unit => exact (hu hb).elim
    | hyperplane => exact (hd ⟨.hyperplane, hb, rfl⟩).elim
    | exceptional i => exact (hd ⟨.exceptional i, hb, rfl⟩).elim
    | point => rfl
  rw [eval_eq_pointInvariant U 1 0 m hp]
  apply pointInvariant_eq_zero_of_dimension_ne U T 1 0 m.card
  rw [map_zero]
  omega

end SurfacePrimary

end AxiomaticGW
