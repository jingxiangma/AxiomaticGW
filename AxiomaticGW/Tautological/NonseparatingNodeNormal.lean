/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.NonseparatingRealization

/-!
# Signed cotangent factor at a newly glued nonseparating node

The two distinguished source markings become the ordered branches of the new
edge. Add one psi factor at each marking, negate their sum, and apply the
existing raw nonseparating graph map. This constructs the expression for the
normal factor `-psi_h - psi_h'` without introducing a product on strata.

Existing psi and gluing realization laws identify the image of this explicit
operation. No self-pullback, excess-intersection identity, boundary square,
automorphism multiplicity, or common-refinement completeness is asserted.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW

open scoped BigOperators

namespace NonseparatingNode

/-- One cotangent factor at branch zero, with every other marking unchanged. -/
def firstPowers {S : Type} : Option (Option S) → ℕ
  | none => 1
  | some _ => 0

/-- One cotangent factor at branch one; old markings retain exponent zero. -/
def secondPowers {S : Type} : Option (Option S) → ℕ
  | none => 0
  | some none => 1
  | some (some _) => 0

theorem firstPowers_sum (S : Type) [Fintype S] :
    ∑ s : Option (Option S), firstPowers s = 1 := by
  simp only [Fintype.sum_option, firstPowers, Finset.sum_const_zero,
    Nat.add_zero]

theorem secondPowers_sum (S : Type) [Fintype S] :
    ∑ s : Option (Option S), secondPowers s = 1 := by
  simp only [Fintype.sum_option, secondPowers, Finset.sum_const_zero,
    Nat.zero_add, Nat.add_zero]

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R}

/-- The first constructed decoration realizes the first node cotangent class. -/
theorem monomial_firstPowers (P : PsiClasses C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g (Option (Option S))) :
    P.monomial g (Option (Option S)) h firstPowers =
      P.psi g (Option (Option S)) h none := by
  simp only [PsiClasses.monomial, Fintype.prod_option, firstPowers,
    pow_zero, pow_one, Finset.prod_const_one, mul_one]

/-- The second constructed decoration realizes the other ordered node branch. -/
theorem monomial_secondPowers (P : PsiClasses C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g (Option (Option S))) :
    P.monomial g (Option (Option S)) h secondPowers =
      P.psi g (Option (Option S)) h (some none) := by
  simp only [PsiClasses.monomial, Fintype.prod_option, secondPowers,
    pow_zero, pow_one, Finset.prod_const_one, mul_one, one_mul]

end NonseparatingNode

namespace StrataModule

variable {g : ℕ} {S : Type} [Fintype S]

/-- Signed normal-factor expression at the new edge, preserving both ordered
branches and the raw gluing convention. This is an actual linear construction. -/
noncomputable def nonseparatingNodeNormal :
    StrataModule g (Option (Option S)) →ₗ[ℚ] StrataModule (g + 1) S :=
  nonseparating.comp
    (-(mulLegPsi NonseparatingNode.firstPowers +
      mulLegPsi NonseparatingNode.secondPowers))

/-- On a graph, the construction retains the two negative branch occurrences. -/
theorem nonseparatingNodeNormal_basis (x : TautologicalStratum g (Option (Option S))) :
    nonseparatingNodeNormal (basis x) =
      -(basis (x.addLegPsi NonseparatingNode.firstPowers).nonseparating +
        basis (x.addLegPsi NonseparatingNode.secondPowers).nonseparating) := by
  simp only [nonseparatingNodeNormal, LinearMap.comp_apply, LinearMap.neg_apply,
    LinearMap.add_apply, map_neg, map_add, mulLegPsi_basis, nonseparating_basis]

/-- One cotangent degree and one gluing degree are added to every source term. -/
theorem nonseparatingNodeNormal_mem_degree {d : ℕ}
    {r : StrataModule g (Option (Option S))} (hr : r ∈ degree d) :
    nonseparatingNodeNormal r ∈ degree (d + 2) := by
  have hfirst := mulLegPsi_mem_degree NonseparatingNode.firstPowers hr
  have hsecond := mulLegPsi_mem_degree NonseparatingNode.secondPowers hr
  rw [NonseparatingNode.firstPowers_sum] at hfirst
  rw [NonseparatingNode.secondPowers_sum] at hsecond
  have hsum := (degree (d + 1)).neg_mem ((degree (d + 1)).add_mem hfirst hsecond)
  simpa only [nonseparatingNodeNormal, LinearMap.comp_apply, LinearMap.neg_apply,
    LinearMap.add_apply, Nat.add_assoc] using nonseparating_mem_degree hsum

end StrataModule

namespace StrataRealization

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
  {g : ℕ} {S : Type} [Fintype S]

attribute [local instance] strataRealizationModule

/-- Realize the constructed node expression from the already existing psi and
gluing laws. This conclusion contains no product of boundary pushforwards. -/
theorem map_nonseparatingNodeNormal
    (A : StrataRealization C g (Option (Option S)))
    (B : StrataRealization C (g + 1) S)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (h : StableArity (g + 1) S)
    (hglue : A.NonseparatingCompatible B N h)
    (hpsi : A.LegPsiCompatible P (StableArity.double_option_iff.mpr h))
    (r : StrataModule g (Option (Option S))) :
    B.map (StrataModule.nonseparatingNodeNormal r) =
      N.push g S h
        (A.map r * -(P.psi g (Option (Option S))
          (StableArity.double_option_iff.mpr h) none +
          P.psi g (Option (Option S))
            (StableArity.double_option_iff.mpr h) (some none))) := by
  change B.map (StrataModule.nonseparating
    (-(StrataModule.mulLegPsi NonseparatingNode.firstPowers r +
      StrataModule.mulLegPsi NonseparatingNode.secondPowers r))) = _
  rw [A.map_nonseparating B N h hglue, map_neg, map_add,
    A.map_mulLegPsi P (StableArity.double_option_iff.mpr h) hpsi,
    A.map_mulLegPsi P (StableArity.double_option_iff.mpr h) hpsi,
    NonseparatingNode.monomial_firstPowers, NonseparatingNode.monomial_secondPowers]
  congr 1
  rw [mul_neg, mul_add]

end StrataRealization

end AxiomaticGW
