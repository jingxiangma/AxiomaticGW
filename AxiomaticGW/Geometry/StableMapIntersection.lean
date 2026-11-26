/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.TwoPointCalibration
public import Mathlib.Algebra.BigOperators.Option

/-!
# Intersection data before stabilization

Mixed correlators use the existing pushed descendant class multiplied by a
stable-curve cotangent monomial. Optional intersection data represents these
same classes on a stable-map space. Its pushforward, projection formula and
proper integration are primitive geometric inputs, not a numerical recursion.
The raw spaces include positive-degree two-point stable maps.
-/

@[expose] public section

namespace AxiomaticGW
universe u
variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

namespace StableMapDescendants

/-- Stable-map powers `d`, followed by stable-curve powers `e`. -/
def mixedClass (M : StableMapDescendants Omega) (P : PsiClasses C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (d e : S → ℕ) : MultilinearMap R (fun _ : S ↦ V) (C.H g S) :=
  (CohFT.multiplyPsi P g S h e).compMultilinearMap (M.descendantClass g S h beta d)

/-- Integrate the existing descendant family against ancestor powers. -/
def mixedInvariant (M : StableMapDescendants Omega) (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (d e : S → ℕ) : MultilinearMap R (fun _ : S ↦ V) R :=
  (I.integrate g S h).compMultilinearMap (M.mixedClass P g S h beta d e)

/-- The mixed numerical expression contains both distinct cotangent theories. -/
theorem mixedInvariant_apply (M : StableMapDescendants Omega) (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (d e : S → ℕ) (a : S → V) :
    M.mixedInvariant P I g S h beta d e a =
      I.integrate g S h (M.descendantClass g S h beta d a * P.monomial g S h e) := rfl

/-- With no ancestor powers, the mixed family is the original descendant family. -/
theorem mixedInvariant_zero_ancestor (M : StableMapDescendants Omega) (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (d : S → ℕ) :
    M.mixedInvariant P I g S h beta d 0 = M.invariant I g S h beta d := by
  ext a
  simp only [mixedInvariant_apply, Pi.zero_def, PsiClasses.monomial_zero, mul_one,
    invariant_apply]

/-- With no stable-map powers, the mixed family is the existing ancestor family. -/
theorem mixedInvariant_zero_descendant (M : StableMapDescendants Omega) (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (e : S → ℕ) :
    M.mixedInvariant P I g S h beta 0 e = Omega.ancestorInvariant P I g S h beta e := by
  ext a
  simp only [mixedInvariant_apply, Pi.zero_def, M.descendantClass_zero,
    GromovWittenTheory.ancestorInvariant_apply]

/-- Relabelling transports both kinds of powers and every state together. -/
theorem mixedInvariant_relabel_apply (M : StableMapDescendants Omega) (P : PsiClasses C)
    (I : StableCurveIntegration C) (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (hS : StableArity g S) (hT : StableArity g T) (b : S ≃ T)
    (beta : B) (d e : T → ℕ) (a : T → V) :
    M.mixedInvariant P I g S hS beta (d ∘ b) (e ∘ b) (a ∘ b) =
      M.mixedInvariant P I g T hT beta d e a := by
  have hd := congrArg (fun f ↦ f a) (M.relabel g S T hS hT b beta (d ∘ b))
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.domDomCongr_apply,
    Function.comp_apply, Equiv.apply_symm_apply] at hd
  change C.rename g S T hS hT b (M.descendantClass g S hS beta (d ∘ b) (a ∘ b)) =
    M.descendantClass g T hT beta d a at hd
  rw [mixedInvariant_apply, mixedInvariant_apply,
    ← I.integrate_rename g S T hS hT b]
  rw [map_mul, hd, P.rename_monomial]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

end StableMapDescendants

/-- Raw intersection data realizing the already supplied full numerical GW family.
This is a geometric input interface, not a construction of stable-map moduli. -/
structure StableMapIntersection (U : UnstableDescendantConventions M I) where
  /-- Even cohomology before stabilization, also at curve-unstable arities. -/
  H : ∀ (_g : ℕ) (S : Type) [Fintype S], B → EvenGradedAlgebra R
  /-- Stable-map cotangent class at a retained marking. -/
  psi : ∀ g S [Fintype S] beta, S → H g S beta
  /-- Evaluation pullback of a state at one marking. -/
  evaluation : ∀ g S [Fintype S] beta, S → V →ₗ[R] H g S beta
  /-- Integration against the virtual class; it is linear, not multiplicative. -/
  integrate : ∀ g S [Fintype S] beta, H g S beta →ₗ[R] R
  /-- Interpretation of the actual numerical family, including two-point tails. -/
  numerical : ∀ g S [Fintype S] beta (d : S → ℕ) (a : S → V),
    integrate g S beta (∏ s, psi g S beta s ^ d s * evaluation g S beta s (a s)) =
      U.invariant g S beta d a

namespace StableMapIntersection
variable {U : UnstableDescendantConventions M I}

/-- The actual product of cotangent powers and evaluation pullbacks. -/
def integrand (G : StableMapIntersection U) (g : ℕ) (S : Type) [Fintype S]
    (beta : B) (d : S → ℕ) (a : S → V) : G.H g S beta :=
  ∏ s, G.psi g S beta s ^ d s * G.evaluation g S beta s (a s)

/-- The node insertion is linear for an arbitrary remaining component decoration. -/
def nodeIntegral (G : StableMapIntersection U) (g : ℕ) (S : Type) [Fintype S]
    (beta : B) (s : S) (x : G.H g S beta) : Module.Dual R V :=
  (G.integrate g S beta).comp ((LinearMap.mulLeft R x).comp (G.evaluation g S beta s))

/-- Two-point node integration is exactly the actual tail correlator. -/
theorem nodeIntegral_twoPoint (G : StableMapIntersection U) (beta : B) (m : ℕ) (y : V) :
    G.nodeIntegral 0 (Fin 2) beta 0
        (G.psi 0 (Fin 2) beta 1 ^ m * G.evaluation 0 (Fin 2) beta 1 y) =
      (SymmetricPerfectPairing.finTwoToBilin (U.invariantMap 0 (Fin 2) beta ![0,m])).flip y := by
  ext x
  change G.integrate 0 (Fin 2) beta
      ((G.psi 0 (Fin 2) beta 1 ^ m * G.evaluation 0 (Fin 2) beta 1 y) *
        G.evaluation 0 (Fin 2) beta 0 x) = _
  have h := G.numerical 0 (Fin 2) beta ![0,m] ![x,y]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero,
    one_mul] at h
  rw [mul_comm, h]
  change _ = SymmetricPerfectPairing.finTwoToBilin
    (U.invariantMap 0 (Fin 2) beta ![0,m]) x y
  rw [SymmetricPerfectPairing.finTwoToBilin_apply, U.invariantMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

end StableMapIntersection

/-- Stabilization pullback and virtual pushforward with their primitive compatibility.
No cotangent difference or rational-tail equation is assumed in this package. -/
structure StableMapStabilization {U : UnstableDescendantConventions M I}
    (G : StableMapIntersection U) where
  /-- Pullback along stabilization of a curve-stable marking set. -/
  pull : ∀ g S [Fintype S] (_h : StableArity g S) beta, C.H g S →ₐ[R] G.H g S beta
  /-- Pushforward after intersecting with the virtual class. -/
  push : ∀ g S [Fintype S] (_h : StableArity g S) beta, G.H g S beta →ₗ[R] C.H g S
  /-- Projection formula for every stable-curve class and stable-map insertion. -/
  projection : ∀ g S [Fintype S] h beta (x : G.H g S beta) (y : C.H g S),
    push g S h beta (x * pull g S h beta y) = push g S h beta x * y
  /-- The virtual pushforward realizes the existing descendant classes. -/
  descendants : ∀ g S [Fintype S] h beta d a,
    push g S h beta (G.integrand g S beta d a) = M.descendantClass g S h beta d a
  /-- Proper integration holds for any class before stabilization. -/
  proper : ∀ g S [Fintype S] h beta (x : G.H g S beta),
    G.integrate g S beta x = I.integrate g S h (push g S h beta x)

namespace StableMapStabilization
variable {U : UnstableDescendantConventions M I} {G : StableMapIntersection U}
  {P : PsiClasses C}

/-- Mixed powers are represented by an actual stable-map integrand. -/
theorem mixedInvariant_eq_integral (T : StableMapStabilization G)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (beta : B)
    (d e : S → ℕ) (a : S → V) :
    M.mixedInvariant P I g S h beta d e a = G.integrate g S beta
      (G.integrand g S beta d a * T.pull g S h beta (P.monomial g S h e)) := by
  rw [T.proper, T.projection, T.descendants, StableMapDescendants.mixedInvariant_apply]

/-- Main-component node integration is the existing mixed invariant with zero node
descendant power. Its node ancestor power is retained in `e`. -/
theorem nodeIntegral_main (T : StableMapStabilization G)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g (Option S)) (beta : B)
    (d : S → ℕ) (e : Option S → ℕ) (a : S → V) (x : V) :
    G.nodeIntegral g (Option S) beta none
        ((∏ s, G.psi g (Option S) beta (some s) ^ d s *
          G.evaluation g (Option S) beta (some s) (a s)) *
          T.pull g (Option S) h beta (P.monomial g (Option S) h e)) x =
      M.mixedInvariant P I g (Option S) h beta (Option.casesOn · 0 d) e
        (Option.casesOn · x a) := by
  rw [T.mixedInvariant_eq_integral]
  change G.integrate g (Option S) beta (_ * _) = _
  congr 1
  simp only [StableMapIntersection.integrand, Fintype.prod_option, pow_zero, one_mul]
  ring

end StableMapStabilization
end AxiomaticGW
