/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.EllipticHodgeEvaluation
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-! # Stable genus-one source vertices on a GKM surface

External markings and edge flags are disjoint labels. The dimension of the elliptic
curve selects exactly one antidiagonal of flag powers for each ordered pair of
Chern indices. The tangent normalization and the evaluation of target insertions
are separate factors in the producer.
-/

@[expose] public section
namespace AxiomaticGW.GKM.EllipticHodge
open PointTarget.DVVCalculation PsiBoundaryExpansion

/-- All possible powers on the flags for one pair of tangent Chern indices. -/
def flagProfiles (f : ℕ) (m : List ℕ) (i j : Fin 2) : Finset (Fin f → ℕ) :=
  let used := m.sum + i.val + j.val
  if used ≤ m.length + f then Finset.finAntidiagonal f (m.length + f - used) else ∅

/-- Membership is precisely the dimension constraint, including vertices with no flags. -/
theorem mem_flagProfiles {f : ℕ} (m : List ℕ) (i j : Fin 2) (k : Fin f → ℕ) :
    k ∈ flagProfiles f m i j ↔ m.sum + i.val + j.val + ∑ s, k s = m.length + f := by
  dsimp only [flagProfiles]
  split <;> simp only [Finset.mem_finAntidiagonal, Finset.notMem_empty, false_iff] <;> omega

variable {L : Type*} [Field L]

/-- The native signed sum over both tangent directions and all incident flag powers. -/
def source {f : ℕ} (m : List ℕ) (u v : L) (flag : Fin f → L)
    (H : Fin 2 → Fin 2 → ((Fin m.length ⊕ Fin f) → ℕ) → ℚ) : L :=
  ∑ j : Fin 2, ∑ i : Fin 2, ∑ k ∈ flagProfiles f m i j,
    (H i j (Sum.elim m.get k) : L) *
      ((-1 : L) ^ (i.val + j.val) * u ^ (-(i.val : ℤ)) * v ^ (-(j.val : ℤ)) *
        ∏ s, (flag s) ^ (-(k s : ℤ) - 1))

/-- Character substitution preserves every signed vertex term. -/
theorem map_source {K : Type*} [Field K] (φ : L →+* K) {f : ℕ} (m : List ℕ)
    (u v : L) (flag : Fin f → L) (H) :
    φ (source m u v flag H) = source m (φ u) (φ v) (fun s ↦ φ (flag s)) H := by
  simp only [source, map_sum, map_mul, map_ratCast, map_pow, map_neg, map_one, map_zpow₀, map_prod]

/-- A marked descendant of excess degree kills the whole vertex for all tangent characters. -/
theorem source_zero_of_excess {f : ℕ} (m : List ℕ) (u v : L) (flag : Fin f → L) (H)
    (over : m.length + f < m.sum) : source m u v flag H = 0 := by
  have empty (i j : Fin 2) : flagProfiles f m i j = ∅ := if_neg (by omega)
  simp only [source, empty, Finset.sum_empty, Finset.sum_const_zero]

/-- The native factor agrees with the sum of actual stable-curve integrals for any
stable vertex. The geometric Hodge input identifies the elliptic line on its source. -/
theorem source_eq_integrals {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C}
    (U : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (T : TailForgetCompatible C)
    (G : GluingForgetfulCompatibility F N)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1) (dvv : PointTarget.DVVRecursion P I)
    (one : value P I 1 [1] = 1 / 24) {f : ℕ} (m : List ℕ)
    (h : StableArity 1 (Fin m.length ⊕ Fin f)) (lambdaOne : C.H 1 (Fin m.length ⊕ Fin f))
    (idHodge : lambdaOne = ellipticBoundary N h) (u v : L) (flag : Fin f → L) :
    source m u v flag nativeMoment = source m u v flag (fun i j d ↦
      I.integrate 1 _ h (P.monomial 1 _ h d *
        ((if i = 0 then 1 else lambdaOne) * (if j = 0 then 1 else lambdaOne)))) := by
  apply congrArg (source m u v flag)
  funext i j d
  exact nativeMoment_eq_integral U F N P K hK T G vol dvv one h lambdaOne idHodge i j d

end AxiomaticGW.GKM.EllipticHodge
