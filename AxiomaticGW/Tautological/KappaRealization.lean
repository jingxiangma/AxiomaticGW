/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.LegPsiRealization

/-!
# Realization of a kappa generator by forgetful pushforward

The decorated corolla carrying one positive kappa class is compared with the
extra-marking psi power by an explicit compatibility law. Together with the
existing external psi realization and fundamental normalization, this law
identifies its image with `PsiClasses.kappa`.

The law is geometric input. It is not implied by a graded linear realization,
and this module neither installs it as an axiom nor asserts multiplicativity
of the realization. The forgotten marking is `none`; old markings are `some`.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

universe u

namespace TautologicalStratum

/-- The corolla with one factor of the positive class `kappa_m`. -/
noncomputable def kappaGenerator (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (m : ℕ+) : TautologicalStratum g S :=
  oneVertex g S h (Finsupp.single m 1) (fun _ ↦ 0)

/-- The extra-marking psi power whose forgetful pushforward defines `kappa_m`. -/
noncomputable def newMarkingPsiGenerator (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (m : ℕ+) : TautologicalStratum g (Option S) :=
  (fundamental g (Option S) h.option).addLegPsi
    (fun t ↦ match t with
      | none => (m : ℕ) + 1
      | some _ => 0)

/-- The kappa generator has the codimension specified by its positive index. -/
theorem kappaGenerator_codimension (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (m : ℕ+) :
    (kappaGenerator g S h m).codimension = (m : ℕ) := by
  simp only [kappaGenerator, oneVertex_codimension, Finsupp.sum_single_index,
    Nat.mul_zero, Nat.mul_one, Finset.sum_const_zero, Nat.add_zero]

/-- The forgotten psi power has codimension one greater than its pushforward. -/
theorem newMarkingPsiGenerator_codimension (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (m : ℕ+) :
    (newMarkingPsiGenerator g S h m).codimension = (m : ℕ) + 1 := by
  simp only [newMarkingPsiGenerator, addLegPsi_codimension,
    fundamental_codimension, Fintype.sum_option, Finset.sum_const_zero,
    Nat.zero_add, Nat.add_zero]

end TautologicalStratum

namespace StrataRealization

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
  {g : ℕ} {S : Type} [Fintype S]

attribute [local instance] strataRealizationModule

/-- Generator-level compatibility with forgetting the extra marking. This
independent law compares two raw strata images before any psi identification. -/
def KappaForgetfulCompatible (A : StrataRealization C g S)
    (B : StrataRealization C g (Option S)) (F : ForgetfulPushforward C I)
    (h : StableArity g S) (m : ℕ+) : Prop :=
  A.map (StrataModule.basis (TautologicalStratum.kappaGenerator g S h m)) =
    F.push g S h
      (B.map (StrataModule.basis (TautologicalStratum.newMarkingPsiGenerator g S h m)))

/-- Derive the geometric kappa image using only the extra-marking psi law,
fundamental normalization, and generator-level forgetful compatibility. -/
theorem map_kappaGenerator (A : StrataRealization C g S)
    (B : StrataRealization C g (Option S)) (F : ForgetfulPushforward C I)
    (P : PsiClasses C) (h : StableArity g S) (m : ℕ+)
    (hκ : A.KappaForgetfulCompatible B F h m)
    (hpsi : B.LegPsiCompatible P h.option)
    (hfund : B.map (StrataModule.basis
      (TautologicalStratum.fundamental g (Option S) h.option)) = 1) :
    A.map (StrataModule.basis (TautologicalStratum.kappaGenerator g S h m)) =
      P.kappa F g S h (m : ℕ) := by
  classical
  have hp : (fun t : Option S ↦ match t with
      | none => (m : ℕ) + 1
      | some _ => 0) = Pi.single none ((m : ℕ) + 1) := by
    funext t
    cases t with
    | none => simp only [Pi.single_eq_same]
    | some s => simp only [Pi.single_eq_of_ne (Option.some_ne_none s)]
  rw [KappaForgetfulCompatible] at hκ
  rw [hκ, TautologicalStratum.newMarkingPsiGenerator, hp,
    B.map_addLegPsi_single P h.option hpsi, hfund, one_mul]
  rfl

end StrataRealization

end AxiomaticGW
