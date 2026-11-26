/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.CorollaForgetful
public import AxiomaticGW.Tautological.ForgetfulKappa
public import AxiomaticGW.Tautological.KappaRealization

/-!
# Realizing a finite corolla forgetful pushforward

The only new geometric realization input is compatibility with the constructed
operation for every positive kappa multi-index and every forgotten psi power
at least two. It contains neither a class-product value nor a distinguished
raw graph. Its zero-vector case recovers the existing generator compatibility.

For one arbitrary kappa factor, the exact two-term expansion and the already
derived cohomological forgetful formula identify the target two-factor corolla
by cancellation. This applies equally to repeated and distinct indices.
Satisfaction of the universal compatibility by a geometric realization is a
remaining hypothesis, not an installed axiom or constructed geometric model.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW

namespace CorollaForgetful

/-- The empty-vector source is precisely the existing new-marking generator. -/
theorem source_zero (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (b : ℕ+) :
    source g S h 0 b = TautologicalStratum.newMarkingPsiGenerator g S h b := by
  rw [TautologicalStratum.newMarkingPsiGenerator, TautologicalStratum.fundamental,
    TautologicalStratum.addLegPsi_oneVertex]
  unfold source
  congr 1
  funext t
  simp only [Pi.add_apply, zero_add]
  rfl

/-- The single-factor source is obtained using the established leg-psi action. -/
theorem source_single (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (a b : ℕ+) [DecidableEq S] :
    source g S h (Finsupp.single a 1) b =
      (TautologicalStratum.kappaGenerator g (Option S) h.option a).addLegPsi
        (Pi.single none ((b : ℕ) + 1)) := by
  classical
  rw [TautologicalStratum.kappaGenerator, TautologicalStratum.addLegPsi_oneVertex]
  unfold source
  congr 1
  funext t
  simp only [Pi.add_apply, zero_add]
  cases t with
  | none => exact (Pi.single_eq_same (M := fun _ : Option S ↦ ℕ) none ((b : ℕ) + 1)).symm
  | some s => exact (Pi.single_eq_of_ne (M := fun _ : Option S ↦ ℕ) (Option.some_ne_none s) ((b : ℕ) + 1)).symm

end CorollaForgetful

namespace StrataRealization

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
  {g : ℕ} {S : Type} [Fintype S]

attribute [local instance] strataRealizationModule

/-- Universal compatibility for the separately constructed finite operation.
This is new geometric input on arbitrary corolla exponent data. -/
def CorollaForgetfulCompatible (A : StrataRealization C g S)
    (B : StrataRealization C g (Option S)) (F : ForgetfulPushforward C I)
    (h : StableArity g S) : Prop :=
  ∀ (α : ℕ+ →₀ ℕ) (b : ℕ+),
    A.map (CorollaForgetful.push g S h α b) =
      F.push g S h (B.map (StrataModule.basis (CorollaForgetful.source g S h α b)))

namespace CorollaForgetfulCompatible

/-- No independent generator law is needed when the universal operation law
is available: take its empty kappa vector. -/
theorem kappaGenerator
    {A : StrataRealization C g S} {B : StrataRealization C g (Option S)}
    {F : ForgetfulPushforward C I} {h : StableArity g S}
    (hc : A.CorollaForgetfulCompatible B F h) (b : ℕ+) :
    A.KappaForgetfulCompatible B F h b := by
  have he := hc 0 b
  rw [CorollaForgetful.push_zero, CorollaForgetful.source_zero] at he
  exact he

end CorollaForgetfulCompatible

/-- Derive the image of a two-factor kappa corolla from universal forgetting,
source generator realization and existing leg-psi multiplication. -/
theorem map_two_kappa_corolla
    (A : StrataRealization C g S) (B : StrataRealization C g (Option S))
    (D : StrataRealization C g (Option (Option S)))
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (Q : ForgetfulSquareCompatibility Fforget F)
    (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C)
    (h : StableArity g S) (a b : ℕ+)
    (hc : A.CorollaForgetfulCompatible B Fforget h)
    (hκ : B.KappaForgetfulCompatible D Fforget h.option a)
    (hpsiB : B.LegPsiCompatible P h.option)
    (hpsiD : D.LegPsiCompatible P h.option.option)
    (hfundB : B.map (StrataModule.basis
      (TautologicalStratum.fundamental g (Option S) h.option)) = 1)
    (hfundD : D.map (StrataModule.basis
      (TautologicalStratum.fundamental g (Option (Option S)) h.option.option)) = 1) :
    A.map (StrataModule.basis (TautologicalStratum.oneVertex g S h
      (Finsupp.single a 1 + Finsupp.single b 1) (fun _ ↦ 0))) =
      P.kappa Fforget g S h (a : ℕ) * P.kappa Fforget g S h (b : ℕ) := by
  classical
  have he := hc (Finsupp.single a 1) b
  rw [CorollaForgetful.push_single, map_add, CorollaForgetful.source_single,
    B.map_addLegPsi_single P h.option hpsiB,
    B.map_kappaGenerator D Fforget P h.option a hκ hpsiD hfundD] at he
  have ht := A.map_kappaGenerator B Fforget P h (a + b)
    (hc.kappaGenerator (a + b)) hpsiB hfundB
  change A.map (StrataModule.basis (TautologicalStratum.oneVertex g S h
    (Finsupp.single (a + b) 1) (fun _ ↦ 0))) = _ at ht
  rw [ht, Q.push_kappa_mul_newPsi N P K hK H g S h (a : ℕ) (b : ℕ),
    PNat.add_coe] at he
  exact add_right_cancel he

end StrataRealization

end AxiomaticGW
