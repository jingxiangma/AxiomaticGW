/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.FormalQuantumProduct
public import Mathlib.Data.Finsupp.Antidiagonal

/-!
# Higher WDVV and the big quantum product

The existing formal big product is commutative without further hypotheses.
Associativity requires the genus-zero boundary relation with an arbitrary
primary background. `GenusZeroHigherBoundary` records that independent
scalar geometric input; state-valued associativity is derived from the
perfect pairing.
-/

@[expose] public section

namespace AxiomaticGW

open Module

universe u

namespace CurveClassGW

variable {R V B : Type u} {ι : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R}

/-- Coefficient of `(x star y) star z` at one primary profile and curve
class. Both the background profile and the effective class are split. -/
noncomputable def formalBigProductAssocLeftCoefficient
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) (x y z : V) : V := by
  classical
  exact ∑ profileSplit ∈ Finset.HasAntidiagonal.antidiagonal n,
    ∑ curveSplit ∈ D.splittings beta,
      Omega.formalBigProductCoefficient I b profileSplit.2 curveSplit.2
        (Omega.formalBigProductCoefficient I b profileSplit.1 curveSplit.1 x y) z

/-- Coefficient of `x star (y star z)` at one primary profile and curve
class. -/
noncomputable def formalBigProductAssocRightCoefficient
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B) (x y z : V) : V := by
  classical
  exact ∑ profileSplit ∈ Finset.HasAntidiagonal.antidiagonal n,
    ∑ curveSplit ∈ D.splittings beta,
      Omega.formalBigProductCoefficient I b profileSplit.1 curveSplit.1 x
        (Omega.formalBigProductCoefficient I b profileSplit.2 curveSplit.2 y z)

/-- Optional higher genus-zero boundary relation. This is the scalar WDVV
identity after grouping the labelled background markings by their two
multiplicity profiles. It is strictly weaker data than state-valued
associativity because the latter is recovered using nondegeneracy. -/
structure GenusZeroHigherBoundary
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) where
  /-- Equality of the two four-point boundary channels for every background
  profile and effective curve class. -/
  higherWDVV : ∀ (n : ι →₀ ℕ) (beta : B) (x y z w : V),
    Omega.pairing.form
        (Omega.formalBigProductAssocLeftCoefficient I b n beta x y z) w =
      Omega.pairing.form
        (Omega.formalBigProductAssocRightCoefficient I b n beta x y z) w

/-- Higher WDVV implies coefficientwise associativity of the formal big
quantum product. -/
theorem formalBigProductCoefficient_assoc
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (H : GenusZeroHigherBoundary Omega I b)
    (n : ι →₀ ℕ) (beta : B) (x y z : V) :
    Omega.formalBigProductAssocLeftCoefficient I b n beta x y z =
      Omega.formalBigProductAssocRightCoefficient I b n beta x y z := by
  apply Omega.pairing.toDual.injective
  ext w
  simpa only [Omega.pairing.toDual_apply] using H.higherWDVV n beta x y z w

/-- Formal associativity, stated as equality of every primary/Novikov
coefficient. -/
theorem formalBigProduct_associative
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (H : GenusZeroHigherBoundary Omega I b)
    (x y z : V) :
    (fun n beta ↦
      Omega.formalBigProductAssocLeftCoefficient I b n beta x y z) =
      fun n beta ↦
        Omega.formalBigProductAssocRightCoefficient I b n beta x y z := by
  funext n beta
  exact Omega.formalBigProductCoefficient_assoc I b H n beta x y z

/-- Genus-zero primary potential. Its coefficient is the integrated primary
invariant divided by the multiplicity factorial; unstable arities are zero. -/
noncomputable def primaryPotential
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) : FormalPotential D ι R := by
  classical
  intro n beta
  exact if h : StableArity 0 (InsertionLabel n) then
    profileWeight R n *
      I.integrate 0 (InsertionLabel n) h
        (Omega.omega 0 (InsertionLabel n) h beta
          (InsertionLabel.primaryState b))
  else 0

@[simp]
theorem primaryPotential_coeff_of_stable
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B)
    (h : StableArity 0 (InsertionLabel n)) :
    Omega.primaryPotential I b n beta =
      profileWeight R n *
        I.integrate 0 (InsertionLabel n) h
          (Omega.omega 0 (InsertionLabel n) h beta
            (InsertionLabel.primaryState b)) := by
  simp [primaryPotential, h]

@[simp]
theorem primaryPotential_coeff_of_unstable
    (Omega : CurveClassGW R V B D C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (n : ι →₀ ℕ) (beta : B)
    (h : ¬StableArity 0 (InsertionLabel n)) :
    Omega.primaryPotential I b n beta = 0 := by
  simp [primaryPotential, h]

end CurveClassGW

end AxiomaticGW
