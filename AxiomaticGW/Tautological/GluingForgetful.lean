/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GluingMarking
public import AxiomaticGW.Tautological.GluingEvaluation
public import AxiomaticGW.CohFT.GluingForgetful

/-!
# Forgetful soundness for explicit undecorated gluing expressions

Class evaluation uses only the component unit, relabelling, and the two raw
gluing pushforwards. Primitive universal-curve base change derives the sum
over placements of an additional marking. Iteration covers any finite number
of new labels. Compatibility identifies this class evaluation with the
existing graph realization; no forgetful graph equation is assumed.
-/

@[expose] public section

namespace AxiomaticGW

universe u

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

namespace StableCurveCohomology

/-- Pull back along the specified ordered sequence of universal forgetful maps. -/
def forgetExtra (C : StableCurveCohomology R) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) : (n : ℕ) → C.H g S →ₐ[R] C.H g (ExtraMarkings n S)
  | 0 => AlgHom.id R (C.H g S)
  | n + 1 => (C.forget g (ExtraMarkings n S) (h.extraMarkings n)).comp
      (C.forgetExtra g S h n)

end StableCurveCohomology

namespace StrataRealization

attribute [local instance] strataRealizationModule

/-- Integrate a pulled-back realized combination against any class upstairs. -/
noncomputable def integrateForgetExtra {g : ℕ} {S : Type} [Fintype S]
    (A : StrataRealization C g S) (I : StableCurveIntegration C)
    (h : StableArity g S) (n : ℕ) (w : C.H g (ExtraMarkings n S)) :
    StrataModule g S →ₗ[ℚ] R :=
  (((I.integrate g (ExtraMarkings n S) (h.extraMarkings n)).comp
    (LinearMap.mulLeft R w)).restrictScalars ℚ).comp
      (((C.forgetExtra g S h n).toLinearMap.restrictScalars ℚ).comp A.map)

/-- This evaluation uses the actual iterated cohomology pullback. -/
theorem integrateForgetExtra_apply {g : ℕ} {S : Type} [Fintype S]
    (A : StrataRealization C g S) (I : StableCurveIntegration C)
    (h : StableArity g S) (n : ℕ) (w : C.H g (ExtraMarkings n S)) (r : StrataModule g S) :
    A.integrateForgetExtra I h n w r =
      I.integrate g (ExtraMarkings n S) (h.extraMarkings n)
        (w * C.forgetExtra g S h n (A.map r)) := rfl

end StrataRealization

namespace GluingExpression

/-- Evaluate the raw gluing construction as an actual cohomology class. -/
noncomputable def classValue (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    {g : ℕ} {S : Type} [Fintype S] : GluingExpression g S → C.H g S
  | @fundamental _ _ _ _ => 1
  | @relabel g S T _ _ e x =>
      C.rename g S T x.stable (x.relabel e).stable e (x.classValue F N)
  | @separating g₁ g₂ S T _ _ x y =>
      F.push g₁ g₂ S T x.stable y.stable (x.classValue F N ⊗ₜ[R] y.classValue F N)
  | @nonseparating g S _ x => N.push g S x.nonseparating.stable (x.classValue F N)

attribute [local instance] strataRealizationModule

/-- The existing primitive graph-map compatibility identifies class evaluation. -/
theorem map_stratum_eq_classValue (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hx : x.Compatible A F N) :
    (A g S).map (StrataModule.basis x.stratum) = x.classValue F N := by
  induction x with
  | fundamental g S h => exact hx
  | relabel e x ih =>
    rw [stratum_relabel, hx.2, ih hx.1]
    rfl
  | separating x y ihx ihy =>
    rw [stratum_separating, hx.2.2, ihx hx.1, ihy hx.2.1]
    rfl
  | nonseparating x ih =>
    rw [stratum_nonseparating, hx.2, ih hx.1]
    rfl

/-- The sum of the actual placed graph classes is the forgetful pullback. -/
theorem sum_classValue_addMarking (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (H : GluingForgetfulCompatibility F N)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) :
    (x.addMarking.map (classValue F N)).sum = C.forget g S x.stable (x.classValue F N) := by
  induction x with
  | fundamental g S h =>
    simp only [addMarking, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, classValue, map_one]
  | @relabel g S T _ _ e x ih =>
    have hn := congrArg (fun f ↦ f (x.classValue F N))
      (C.forget_natural g S T x.stable (x.relabel e).stable e)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hn
    simp only [addMarking, List.map_map, Function.comp_def, classValue]
    rw [hn, ← ih, map_list_sum, List.map_map]
    rfl
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    rw [classValue, H.separating, ← ihx, ← ihy]
    simp only [addMarking, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, classValue, map_list_sum, List.map_map]
    congr 1
    · induction x.addMarking with
      | nil => simp only [List.map_nil, List.sum_nil, map_zero, TensorProduct.zero_tmul]
      | cons z zs ih =>
        simp only [List.map_cons, List.sum_cons, map_add, TensorProduct.add_tmul, ih]
    · induction y.addMarking with
      | nil => simp only [List.map_nil, List.sum_nil, map_zero, TensorProduct.tmul_zero]
      | cons z zs ih =>
        simp only [List.map_cons, List.sum_cons, map_add, TensorProduct.tmul_add, ih]
  | @nonseparating g S _ x ih =>
    rw [classValue, H.nonseparating, ← ih]
    simp only [addMarking, List.map_map, Function.comp_def, classValue,
      map_list_sum, List.map_map]

/-- Iterating the proved one-marking formula preserves every placement multiplicity. -/
theorem sum_classValue_addMarkings (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (H : GluingForgetfulCompatibility F N)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (n : ℕ) :
    ((x.addMarkings n).map (classValue F N)).sum =
      C.forgetExtra g S x.stable n (x.classValue F N) := by
  induction n with
  | zero =>
    simp only [addMarkings, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, StableCurveCohomology.forgetExtra, AlgHom.id_apply]
  | succ n ih =>
    rw [addMarkings, List.map_flatMap, List.flatMap_def, List.sum_flatten]
    simp only [List.map_map, Function.comp_def]
    have heq : ((x.addMarkings n).map fun z ↦ (z.addMarking.map (classValue F N)).sum) =
        (x.addMarkings n).map fun z ↦
          C.forget g (ExtraMarkings n S) (x.stable.extraMarkings n) (z.classValue F N) := by
      apply List.map_congr_left
      intro z _
      exact z.sum_classValue_addMarking F N H
    rw [heq]
    change ((x.addMarkings n).map
      ((C.forget g (ExtraMarkings n S) (x.stable.extraMarkings n)) ∘ classValue F N)).sum = _
    rw [← List.map_map, ← map_list_sum, ih]
    rfl

/-- Compatible realizations give the forgetful graph formula as a theorem.
Only compatibility of the source and the finitely many output expressions is required. -/
theorem sum_map_stratum_addMarkings
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (n : ℕ) (hx : x.Compatible A F N)
    (hz : ∀ z ∈ x.addMarkings n, z.Compatible A F N) :
    ((x.addMarkings n).map fun z ↦
      (A g (ExtraMarkings n S)).map (StrataModule.basis z.stratum)).sum =
      C.forgetExtra g S x.stable n ((A g S).map (StrataModule.basis x.stratum)) := by
  rw [x.map_stratum_eq_classValue A F N hx]
  have heq : ((x.addMarkings n).map fun z ↦
      (A g (ExtraMarkings n S)).map (StrataModule.basis z.stratum)) =
      (x.addMarkings n).map (classValue F N) := by
    apply List.map_congr_left
    intro z hmem
    exact z.map_stratum_eq_classValue A F N (hz z hmem)
  rw [heq, x.sum_classValue_addMarkings F N H n]

/-- An arbitrary upstairs insertion pairs with the sum of all placed graphs.
No pullback of that insertion, and hence no decorated pullback shortcut, is used. -/
theorem integrateForgetExtra_eq_sum
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (n : ℕ) (hx : x.Compatible A F N)
    (hz : ∀ z ∈ x.addMarkings n, z.Compatible A F N) (w : C.H g (ExtraMarkings n S)) :
    (A g S).integrateForgetExtra I x.stable n w (StrataModule.basis x.stratum) =
      ((x.addMarkings n).map fun z ↦ (A g (ExtraMarkings n S)).integrateAgainst I
        (x.stable.extraMarkings n) w (StrataModule.basis z.stratum)).sum := by
  let L := (I.integrate g (ExtraMarkings n S) (x.stable.extraMarkings n)).comp
    (LinearMap.mulLeft R w)
  change L (C.forgetExtra g S x.stable n ((A g S).map (StrataModule.basis x.stratum))) = _
  rw [← x.sum_map_stratum_addMarkings A F N H n hx hz, map_list_sum, List.map_map]
  rfl

end GluingExpression

end AxiomaticGW
