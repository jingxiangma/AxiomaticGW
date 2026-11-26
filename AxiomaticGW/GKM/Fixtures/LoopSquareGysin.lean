/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.LoopSquareGluing

/-!
# The seven ordered correspondences for the held nonseparating gluing

All operators are constructed from existing relabelling, gluing pullback and
raw proper pushforward maps. The two disjoint-node constructions retain the
exchange of node pairs, including the componentwise marking exchanges in the
parallel case. Ordered graph bindings concern only finite combinatorics.

`SelfGysinCompatible` is a new, explicit geometric obligation on every source
class. It is not derived from graph enumeration, supplied at the unit only,
or instantiated here. Its geometric source is refined Gysin base change on
the gluing fibre product, with the signed excess line on shared nodes; see
Schmitt--van Zelm, DOI 10.1007/s00029-020-00603-4, Propositions 2.13 and 2.16.
No geometric model, Hodge class, or global strata product is constructed.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.LoopSquareGysin

open LoopSquareGluing
open scoped BigOperators TensorProduct

abbrev SourceLabels := Option (Option (Fin 1))
abbrev DoubleLabels := Option (Option SourceLabels)

theorem sourceStable : StableArity 1 SourceLabels :=
  StableArity.double_option_iff.mpr HodgeDegreeOneRealization.stable

theorem doubleStable : StableArity 0 DoubleLabels :=
  StableArity.double_option_iff.mpr sourceStable

theorem rationalStable : StableArity 0 (Option (Fin 2)) := by
  unfold StableArity
  decide

theorem ellipticStable : StableArity 1 (Option (Fin 1)) := by
  unfold StableArity
  decide

/-- Exchange the two node pairs, preserving their internal orders and the old leg. -/
def pairExchange : Equiv.Perm DoubleLabels where
  toFun
    | none => some (some none)
    | some none => some (some (some none))
    | some (some none) => none
    | some (some (some none)) => some none
    | some (some (some (some s))) => some (some (some (some s)))
  invFun
    | none => some (some none)
    | some none => some (some (some none))
    | some (some none) => none
    | some (some (some none)) => some none
    | some (some (some (some s))) => some (some (some (some s)))
  left_inv x := by rcases x with _ | (_ | (_ | (_ | s))) <;> rfl
  right_inv x := by rcases x with _ | (_ | (_ | (_ | s))) <;> rfl

/-- The retained edge is edge zero; edge one is glued by the source boundary map. -/
def doubleFlagLabel (e b : Fin 2) : DoubleLabels :=
  if e = 0 then
    if b = 0 then some (some none) else some (some (some none))
  else if b = 0 then none else some none

theorem pairExchange_flags (e b : Fin 2) :
    pairExchange (doubleFlagLabel e b) = doubleFlagLabel (Equiv.swap 0 1 e) b := by
  fin_cases e <;> fin_cases b <;> rfl

theorem pairExchange_old (s : Fin 1) :
    pairExchange (some (some (some (some s)))) = some (some (some (some s))) := rfl

/-- Exchange the gluing and retained branch markings on each ordered component. -/
def rationalExchange : Equiv.Perm (Option (Fin 2)) := Equiv.swap none (some 0)

def ellipticExchange : Equiv.Perm (Option (Fin 1)) := Equiv.swap none (some 0)

def componentExchange : Equiv.Perm (Option (Fin 2) ⊕ Option (Fin 1)) :=
  rationalExchange.sumCongr ellipticExchange

/-- The separating node is edge one and the retained parallel edge is edge zero. -/
def parallelFlagLabel (e b : Fin 2) : Option (Fin 2) ⊕ Option (Fin 1) :=
  if b = 0 then .inl (if e = 0 then some 0 else none)
  else .inr (if e = 0 then some 0 else none)

theorem componentExchange_flags (e b : Fin 2) :
    componentExchange (parallelFlagLabel e b) =
      parallelFlagLabel (Equiv.swap 0 1 e) b := by
  fin_cases e <;> fin_cases b <;> decide +kernel

theorem componentExchange_old :
    componentExchange (.inl (some 1)) = .inl (some 1) := by
  decide +kernel

/-- Both accepted source placements are retained as distinct ordered maps. -/
def parallelLabels : Fin 2 → (Fin 2 ⊕ Fin 1 ≃ SourceLabels) :=
  ![firstLabels, secondLabels]

theorem parallelLabels_swap :
    parallelLabels 1 = (parallelLabels 0).trans (swapDoubleOption (Fin 1)) := by
  ext x
  rcases x with i | i <;> fin_cases i <;> rfl

/-- The two shared components have identity and exchanged right-hand branches. -/
theorem shared_orbit_binding :
    LoopSquareRefinements.orbits LoopSquareRefinements.target =
      Finset.univ.image (fun b : Fin 2 ↦ LoopSquareRefinements.orbit
        LoopSquareRefinements.target (((0 : Fin 1), 0), ((0 : Fin 1), b))) := by
  decide +kernel

/-- The other double-loop contraction retains the other ordered edge. -/
theorem double_orbit_binding :
    LoopSquareRefinements.orbits LoopSquareRefinements.doubleLoop =
      {LoopSquareRefinements.orbit LoopSquareRefinements.doubleLoop (((0 : Fin 2), 0), ((1 : Fin 2), 0))} := by
  decide +kernel

/-- All four relative branch choices occur, with no additional quotient. -/
theorem parallel_orbit_binding :
    LoopSquareRefinements.orbits LoopSquareRefinements.parallel =
      Finset.univ.image (fun ij : Fin 2 × Fin 2 ↦ LoopSquareRefinements.orbit
        LoopSquareRefinements.parallel (((0 : Fin 2), ij.1), ((1 : Fin 2), ij.2))) := by
  decide +kernel

/-- The pair exchange agrees with the actual two contraction flag maps. -/
theorem double_contraction_flags (b : Fin 2) :
    pairExchange (doubleFlagLabel
      (LoopSquareRefinements.flagMap
        (G := LoopSquareRefinements.doubleLoop) ((0 : Fin 2), 0) b).1
      (LoopSquareRefinements.flagMap
        (G := LoopSquareRefinements.doubleLoop) ((0 : Fin 2), 0) b).2) =
    doubleFlagLabel
      (LoopSquareRefinements.flagMap
        (G := LoopSquareRefinements.doubleLoop) ((1 : Fin 2), 0) b).1
      (LoopSquareRefinements.flagMap
        (G := LoopSquareRefinements.doubleLoop) ((1 : Fin 2), 0) b).2 := by
  fin_cases b <;> rfl

/-- Component exchanges preserve each chosen target branch order. -/
theorem parallel_contraction_flags (j b : Fin 2) :
    componentExchange (parallelFlagLabel
      (LoopSquareRefinements.flagMap
        (G := LoopSquareRefinements.parallel) ((0 : Fin 2), j) b).1
      (LoopSquareRefinements.flagMap
        (G := LoopSquareRefinements.parallel) ((0 : Fin 2), j) b).2) =
    parallelFlagLabel
      (LoopSquareRefinements.flagMap
        (G := LoopSquareRefinements.parallel) ((1 : Fin 2), j) b).1
      (LoopSquareRefinements.flagMap
        (G := LoopSquareRefinements.parallel) ((1 : Fin 2), j) b).2 := by
  fin_cases j <;> fin_cases b <;> decide +kernel

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

def outerPush (N : NonseparatingPushforward C I) :
    C.H 1 SourceLabels →ₗ[R] C.H 2 (Fin 1) :=
  N.push 1 (Fin 1) HodgeDegreeOneRealization.stable

def outerPull (C : StableCurveCohomology R) :
    C.H 2 (Fin 1) →ₐ[R] C.H 1 SourceLabels :=
  C.nonseparating 1 (Fin 1) HodgeDegreeOneRealization.stable

def branchSwap (C : StableCurveCohomology R) :
    C.H 1 SourceLabels ≃ₐ[R] C.H 1 SourceLabels :=
  C.rename 1 SourceLabels SourceLabels sourceStable sourceStable (swapDoubleOption (Fin 1))

def normalClass (P : PsiClasses C) : C.H 1 SourceLabels :=
  -(P.psi 1 SourceLabels sourceStable none + P.psi 1 SourceLabels sourceStable (some none))

def doublePush (N : NonseparatingPushforward C I) :
    C.H 0 DoubleLabels →ₗ[R] C.H 1 SourceLabels :=
  N.push 0 SourceLabels sourceStable

/-- The right contraction closes the OTHER pair; its relabelling is essential. -/
def doubleOtherPull (C : StableCurveCohomology R) :
    C.H 1 SourceLabels →ₐ[R] C.H 0 DoubleLabels :=
  (C.rename 0 DoubleLabels DoubleLabels doubleStable doubleStable pairExchange).toAlgHom.comp
    (C.nonseparating 0 SourceLabels sourceStable)

def parallelPush (F : SeparatingPushforward C I) (i : Fin 2) :
    (C.H 0 (Option (Fin 2)) ⊗[R] C.H 1 (Option (Fin 1))) →ₗ[R] C.H 1 SourceLabels :=
  (C.rename 1 (Fin 2 ⊕ Fin 1) SourceLabels (StableArity.separating rationalStable ellipticStable)
    sourceStable (parallelLabels i)).toLinearMap.comp
      (F.push 0 1 (Fin 2) (Fin 1) rationalStable ellipticStable)

/-- The inverse retained-label transport precedes separating pullback. -/
def parallelPull (C : StableCurveCohomology R) (i : Fin 2) :
    C.H 1 SourceLabels →ₐ[R]
      (C.H 0 (Option (Fin 2)) ⊗[R] C.H 1 (Option (Fin 1))) :=
  (C.separating 0 1 (Fin 2) (Fin 1) rationalStable ellipticStable).comp
    (C.rename 1 SourceLabels (Fin 2 ⊕ Fin 1) sourceStable
      (StableArity.separating rationalStable ellipticStable) (parallelLabels i).symm).toAlgHom

/-- Interchange each component's old gluing branch and future gluing branch. -/
def componentPull (C : StableCurveCohomology R) :
    (C.H 0 (Option (Fin 2)) ⊗[R] C.H 1 (Option (Fin 1))) →ₐ[R]
      (C.H 0 (Option (Fin 2)) ⊗[R] C.H 1 (Option (Fin 1))) :=
  Algebra.TensorProduct.map
    (C.rename 0 (Option (Fin 2)) (Option (Fin 2))
      rationalStable rationalStable rationalExchange).toAlgHom
    (C.rename 1 (Option (Fin 1)) (Option (Fin 1))
      ellipticStable ellipticStable ellipticExchange).toAlgHom

/-- The seven ordered contributions, as an actual linear operator on all classes. -/
def refinementOperator (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) :
    C.H 1 SourceLabels →ₗ[R] C.H 1 SourceLabels :=
  (LinearMap.mulRight R (normalClass P)).comp
      (LinearMap.id + (branchSwap C).toLinearMap) +
    (doublePush N).comp (doubleOtherPull C).toLinearMap +
    ∑ i : Fin 2, ∑ j : Fin 2,
      (parallelPush F i).comp ((componentPull C).toLinearMap.comp (parallelPull C j).toLinearMap)

/-- Explicit, uninstantiated geometric Gysin base-change and excess obligation.
This compares maps on every source class, with no supplied product value. -/
def SelfGysinCompatible (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) : Prop :=
  (outerPull C).toLinearMap.comp (outerPush N) = refinementOperator F N P

theorem selfGysin_apply (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (H : SelfGysinCompatible F N P) (z : C.H 1 SourceLabels) :
    outerPull C (outerPush N z) = refinementOperator F N P z :=
  congrArg (fun f : C.H 1 SourceLabels →ₗ[R] C.H 1 SourceLabels ↦ f z) H

/-- The general projection reduction needs no self-intersection hypothesis. -/
theorem push_mul_push (N : NonseparatingPushforward C I)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity (g + 1) S)
    (x y : C.H g (Option (Option S))) :
    N.push g S h x * N.push g S h y =
      N.push g S h (C.nonseparating g S h (N.push g S h x) * y) :=
  (N.projection_formula g S h (N.push g S h x) y).symm

/-- Branch swapping after the separating map disappears under the final raw gluing. -/
theorem parallel_push_swap (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I)
    (w : C.H 0 (Option (Fin 2)) ⊗[R] C.H 1 (Option (Fin 1))) :
    outerPush N (parallelPush F 1 w) = outerPush N (parallelPush F 0 w) := by
  unfold parallelPush
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
  rw [parallelLabels_swap, C.rename_trans]
  exact congrArg (fun f : C.H 1 SourceLabels →ₗ[R] C.H 2 (Fin 1) ↦ f
    (C.rename 1 (Fin 2 ⊕ Fin 1) SourceLabels
      (StableArity.separating rationalStable ellipticStable) sourceStable (parallelLabels 0)
        (F.push 0 1 (Fin 2) (Fin 1) rationalStable ellipticStable w)))
    (N.push_swap 1 (Fin 1) HodgeDegreeOneRealization.stable)

/-- All class pullbacks are unital, but every source occurrence remains explicit. -/
theorem refinementOperator_one (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) :
    refinementOperator F N P 1 =
      normalClass P + normalClass P + doublePush N 1 +
        (parallelPush F 0 1 + parallelPush F 0 1) +
        (parallelPush F 1 1 + parallelPush F 1 1) := by
  simp only [refinementOperator, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, LinearMap.id_apply, AlgEquiv.toLinearMap_apply,
    AlgHom.toLinearMap_apply, map_one, add_mul, one_mul,
    Fin.sum_univ_two]
  abel

/-- Arbitrary insertions follow from the new map identity and existing projection. -/
theorem product_of_selfGysin (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (H : SelfGysinCompatible F N P) (x y : C.H 1 SourceLabels) :
    outerPush N x * outerPush N y =
      outerPush N (refinementOperator F N P x * y) := by
  calc
    outerPush N x * outerPush N y =
        outerPush N (outerPull C (outerPush N x) * y) :=
      (N.projection_formula 1 (Fin 1) HodgeDegreeOneRealization.stable
        (outerPush N x) y).symm
    _ = outerPush N (refinementOperator F N P x * y) := by
      rw [selfGysin_apply F N P H]

/-- The unit specialization is derived after retaining the seven arbitrary-class maps. -/
theorem raw_loop_square (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (H : SelfGysinCompatible F N P) :
    outerPush N 1 ^ 2 =
      outerPush N (normalClass P) + outerPush N (normalClass P) +
        outerPush N (doublePush N 1) +
        (outerPush N (parallelPush F 0 1) + outerPush N (parallelPush F 0 1)) +
        (outerPush N (parallelPush F 0 1) + outerPush N (parallelPush F 0 1)) := by
  rw [pow_two, product_of_selfGysin F N P H, mul_one, refinementOperator_one]
  simp only [map_add, parallel_push_swap]

end AxiomaticGW.GKM.LoopSquareGysin
