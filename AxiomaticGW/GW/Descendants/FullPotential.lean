/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.Exceptional
public import AxiomaticGW.GW.Descendants.Potentials

/-!
# Unstable descendant conventions

Stable-map descendants in this project land in stable-curve cohomology and
therefore exist only for stable curve arities. This file permits the missing
numerical unstable correlators to be supplied explicitly. It does not assign
positive-degree unstable invariants by fiat.

The stable string and dilaton laws and the exceptional unstable recurrences
together imply equations valid for every finite marking type.
-/

@[expose] public section

namespace AxiomaticGW

open Module

universe u

/-- Combine stable descendant invariants with an explicitly supplied family
of unstable numerical correlators. -/
noncomputable def extendedDescendantInvariant
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    (M : StableMapDescendants Omega) (I : StableCurveIntegration C)
    (unstable : ∀ (_g : ℕ) (S : Type) [Fintype S], B → (S → ℕ) →
      MultilinearMap R (fun _ : S ↦ V) R)
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (k : S → ℕ)
    (a : S → V) : R := by
  classical
  exact if h : StableArity g S then M.invariant I g S h beta k a
    else unstable g S beta k a

/-- Numerical data outside stable curve arities. Degree-zero unstable
values use the zero convention. The metric and genus-one initial value enter
as explicit corrections to the equations, not as unstable invariants. -/
structure UnstableDescendantConventions
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    (M : StableMapDescendants Omega) (I : StableCurveIntegration C) where
  /-- Numerical correlators; only their unstable-arity values are used. -/
  unstableInvariant : ∀ (_g : ℕ) (S : Type) [Fintype S],
    B → (S → ℕ) → MultilinearMap R (fun _ : S ↦ V) R
  /-- The auxiliary degree-zero convention is zero in every unstable arity. -/
  unstable_zero : ∀ (g : ℕ) (S : Type) [Fintype S]
      (_h : ¬StableArity g S) (k : S → ℕ),
    unstableInvariant g S 0 k = 0
  /-- Unstable data are natural under simultaneous relabelling. -/
  unstable_relabel : ∀ (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (_hS : ¬StableArity g S) (_hT : ¬StableArity g T)
      (e : S ≃ T) (beta : B) (k : S → ℕ),
    (unstableInvariant g S beta k).domDomCongr e =
      unstableInvariant g T beta (fun t ↦ k (e.symm t))
  /-- Numerical invariants vanish outside their virtual dimension. -/
  unstable_degree : ∀ (g : ℕ) (S : Type) [Fintype S]
      (_h : ¬StableArity g S) (beta : B) (k p : S → ℕ) (a : S → V),
    (∀ s, a s ∈ Omega.graded.degree (p s)) →
    ((∑ s, p s : ℕ) : ℤ) + ((∑ s, k s : ℕ) : ℤ) ≠
      GWVirtualDimension Omega.graded.dimension g (Fintype.card S)
        (Omega.c1Degree beta) →
    unstableInvariant g S beta k a = 0
  /-- The degree-zero genus-one unit-descendant value. Geometry identifies
  this with the Euler characteristic of the target divided by 24. -/
  genusOneDilaton : R
  /-- String recurrence across unstable arities, including the exceptional
  three-point metric term. -/
  string_unstable : ∀ (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
      (_h : ¬StableArity g S) (beta : B) (k : S → ℕ) (a : S → V),
    extendedDescendantInvariant M I unstableInvariant g (Option S) beta
        (fun | none => 0 | some s => k s)
        (fun | none => Omega.unit | some s => a s) =
      (∑ s, if k s = 0 then 0 else
        extendedDescendantInvariant M I unstableInvariant g S beta
          (lowerPower k s) a) +
        stringCorrection Omega.pairing g S beta k a
  /-- The signed dilaton recurrence, with its target-dependent genus-one
  correction. Positive curve classes have no exceptional term. -/
  dilaton_unstable : ∀ (g : ℕ) (S : Type) [Fintype S]
      (_h : ¬StableArity g S) (beta : B) (k : S → ℕ) (a : S → V),
    extendedDescendantInvariant M I unstableInvariant g (Option S) beta
        (fun | none => 1 | some s => k s)
        (fun | none => Omega.unit | some s => a s) =
      dilatonCoefficient R g S *
        extendedDescendantInvariant M I unstableInvariant g S beta k a +
        dilatonCorrection genusOneDilaton g S beta

namespace UnstableDescendantConventions

variable {R V B : Type u} {ι : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Numerical descendant invariant for every arity. At degree zero,
unstable values are auxiliary zeros rather than geometric invariants. -/
noncomputable def invariant (U : UnstableDescendantConventions M I)
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (k : S → ℕ)
    (a : S → V) : R :=
  extendedDescendantInvariant M I U.unstableInvariant g S beta k a

/-- The full numerical invariant is multilinear in its state insertions. -/
noncomputable def invariantMap (U : UnstableDescendantConventions M I)
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (k : S → ℕ) :
    MultilinearMap R (fun _ : S ↦ V) R := by
  classical
  exact if h : StableArity g S then M.invariant I g S h beta k
    else U.unstableInvariant g S beta k

/-- Evaluation of the bundled multilinear invariant. -/
theorem invariantMap_apply (U : UnstableDescendantConventions M I)
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (k : S → ℕ) (a : S → V) :
    U.invariantMap g S beta k a = U.invariant g S beta k a := by
  classical
  by_cases h : StableArity g S <;>
    simp only [invariantMap, invariant, extendedDescendantInvariant, h, ↓reduceDIte]

/-- On stable arities the extension agrees with the existing invariant. -/
theorem invariant_of_stable (U : UnstableDescendantConventions M I)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (k : S → ℕ) (a : S → V) :
    U.invariant g S beta k a = M.invariant I g S h beta k a := by
  simp only [invariant, extendedDescendantInvariant, h, ↓reduceDIte,
    StableMapDescendants.invariant_apply]

/-- On unstable arities the extension uses the supplied numerical data. -/
theorem invariant_of_unstable (U : UnstableDescendantConventions M I)
    (g : ℕ) (S : Type) [Fintype S] (h : ¬StableArity g S)
    (beta : B) (k : S → ℕ) (a : S → V) :
    U.invariant g S beta k a = U.unstableInvariant g S beta k a := by
  simp only [invariant, extendedDescendantInvariant, h, ↓reduceDIte]

/-- Every degree-zero unstable numerical invariant has the zero convention. -/
theorem invariant_zero_of_unstable (U : UnstableDescendantConventions M I)
    (g : ℕ) (S : Type) [Fintype S] (h : ¬StableArity g S)
    (k : S → ℕ) (a : S → V) : U.invariant g S 0 k a = 0 := by
  rw [U.invariant_of_unstable g S h, U.unstable_zero g S h]
  rfl

/-- The zero-point auxiliary invariant in degree zero vanishes. -/
theorem zeroPoint_zero (U : UnstableDescendantConventions M I) :
    U.unstableInvariant 0 Empty 0 (fun s ↦ nomatch s) (fun s ↦ nomatch s) = 0 := by
  rw [U.unstable_zero 0 Empty (by norm_num [StableArity])]
  rfl

/-- The one-point auxiliary invariant in degree zero vanishes. -/
theorem onePoint_zero (U : UnstableDescendantConventions M I)
    (k : Fin 1 → ℕ) (a : Fin 1 → V) : U.unstableInvariant 0 (Fin 1) 0 k a = 0 := by
  rw [U.unstable_zero 0 (Fin 1) (by norm_num [StableArity])]
  rfl

/-- The two-point degree-zero numerical convention is zero. The metric
occurs in the string correction and is not this auxiliary invariant. -/
theorem twoPoint_zero (U : UnstableDescendantConventions M I) (a : Fin 2 → V) :
    U.unstableInvariant 0 (Fin 2) 0 (fun _ ↦ 0) a = 0 := by
  rw [U.unstable_zero 0 (Fin 2) (by norm_num [StableArity])]
  rfl

/-- The full invariant is natural under relabelling of powers and inputs. -/
theorem invariant_relabel (U : UnstableDescendantConventions M I)
    (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (e : S ≃ T) (beta : B) (k : S → ℕ) :
    (U.invariantMap g S beta k).domDomCongr e =
      U.invariantMap g T beta (fun t ↦ k (e.symm t)) := by
  classical
  by_cases hS : StableArity g S
  · have hT := (StableArity.equiv e).mp hS
    simp only [invariantMap, hS, hT, ↓reduceDIte]
    exact M.invariant_relabel I g S T hS hT e beta k
  · have hT : ¬StableArity g T := fun h ↦ hS ((StableArity.equiv e).mpr h)
    simp only [invariantMap, hS, hT, ↓reduceDIte]
    exact U.unstable_relabel g S T hS hT e beta k

/-- The full invariant vanishes outside the integer virtual dimension. -/
theorem invariant_eq_zero_of_degree_ne (U : UnstableDescendantConventions M I)
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (k p : S → ℕ) (a : S → V)
    (ha : ∀ s, a s ∈ Omega.graded.degree (p s))
    (hne : ((∑ s, p s : ℕ) : ℤ) + ((∑ s, k s : ℕ) : ℤ) ≠
      GWVirtualDimension Omega.graded.dimension g (Fintype.card S)
        (Omega.c1Degree beta)) : U.invariant g S beta k a = 0 := by
  by_cases h : StableArity g S
  · rw [U.invariant_of_stable g S h]
    exact M.invariant_eq_zero_of_degree_ne I g S h beta k p a ha hne
  · rw [U.invariant_of_unstable g S h]
    exact U.unstable_degree g S h beta k p a ha hne

/-- The global string equation includes its degree-zero metric correction. -/
theorem global_string (U : UnstableDescendantConventions M I)
    (L : DescendantStringDilatonLaws M I)
    (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (beta : B) (k : S → ℕ) (a : S → V) :
    U.invariant g (Option S) beta
        (fun | none => 0 | some s => k s)
        (fun | none => Omega.unit | some s => a s) =
      (∑ s, if k s = 0 then 0 else U.invariant g S beta (lowerPower k s) a) +
        stringCorrection Omega.pairing g S beta k a := by
  by_cases h : StableArity g S
  · rw [stringCorrection_eq_zero_of_stable Omega.pairing g S beta k a h, add_zero,
      U.invariant_of_stable g (Option S) (StableArity.option h)]
    refine (L.string g S h beta k a).trans ?_
    apply Finset.sum_congr rfl
    intro s _hs
    split_ifs
    · rfl
    · rw [U.invariant_of_stable g S h]
  · exact U.string_unstable g S h beta k a

/-- The global dilaton equation has a signed coefficient and an exceptional
constant at degree-zero genus one with no other markings. -/
theorem global_dilaton (U : UnstableDescendantConventions M I)
    (L : DescendantStringDilatonLaws M I)
    (g : ℕ) (S : Type) [Fintype S]
    (beta : B) (k : S → ℕ) (a : S → V) :
    U.invariant g (Option S) beta
        (fun | none => 1 | some s => k s)
        (fun | none => Omega.unit | some s => a s) =
      dilatonCoefficient R g S * U.invariant g S beta k a +
        dilatonCorrection U.genusOneDilaton g S beta := by
  by_cases h : StableArity g S
  · rw [dilatonCorrection_eq_zero_of_stable U.genusOneDilaton g S beta h, add_zero,
      dilatonCoefficient_eq_natCast R g S h,
      U.invariant_of_stable g (Option S) (StableArity.option h),
      U.invariant_of_stable g S h]
    exact L.dilaton g S h beta k a
  · exact U.dilaton_unstable g S h beta k a

/-- Full genus-`g` descendant potential, including explicitly supplied
unstable coefficients. -/
noncomputable def fullDescendantPotential
    (U : UnstableDescendantConventions M I) (b : Basis ι R V) (g : ℕ) :
    FormalPotential D (DescendantVariable ι) R := by
  classical
  intro n beta
  exact profileWeight R n *
    U.invariant g (InsertionLabel n) beta
      (InsertionLabel.power (n := n)) (InsertionLabel.state (n := n) b)

/-- The full potential agrees with the existing stable potential at every
stable profile. -/
theorem fullDescendantPotential_coeff_of_stable
    (U : UnstableDescendantConventions M I) (b : Basis ι R V) (g : ℕ)
    (n : DescendantVariable ι →₀ ℕ) (beta : B)
    (h : StableArity g (InsertionLabel n)) :
    U.fullDescendantPotential b g n beta =
      Omega.descendantPotential M I b g n beta := by
  rw [GromovWittenTheory.descendantPotential_coeff_of_stable _ _ _ _ _ _ _ h]
  simp only [fullDescendantPotential]
  rw [U.invariant_of_stable g (InsertionLabel n) h]

/-- At an unstable profile, the coefficient is exactly the declared
convention with the standard multiplicity weight. -/
theorem fullDescendantPotential_coeff_of_unstable
    (U : UnstableDescendantConventions M I) (b : Basis ι R V) (g : ℕ)
    (n : DescendantVariable ι →₀ ℕ) (beta : B)
    (h : ¬StableArity g (InsertionLabel n)) :
    U.fullDescendantPotential b g n beta =
      profileWeight R n * U.unstableInvariant g (InsertionLabel n) beta
        (InsertionLabel.power (n := n)) (InsertionLabel.state (n := n) b) := by
  simp only [fullDescendantPotential]
  rw [U.invariant_of_unstable g (InsertionLabel n) h]

end UnstableDescendantConventions

end AxiomaticGW
