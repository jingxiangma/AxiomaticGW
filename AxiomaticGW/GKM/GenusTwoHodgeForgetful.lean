/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Combinatorics.MarkingPowers
public import AxiomaticGW.GKM.GenusTwoLocalizationIntegrand
public import AxiomaticGW.Tautological.ForgetfulIntegrals
public import AxiomaticGW.Tautological.ForgetfulKappa

/-! # Geometric relabeling and forgetful laws for genus-two Hodge moments

The Hodge bundle pulls back when a marking is forgotten. Its two Chern classes
and the universal-curve maps determine the string and dilaton recurrences.
The base normalization for the dilaton coefficient is κ₀ = 2 on the unmarked curve.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoLocalizationClass
open GenusTwoVertexHodgeReduction PsiBoundaryExpansion

variable {C : StableCurveCohomology ℚ}

/-- Naturality of the two positive Hodge classes on ordered source curves. -/
structure HodgeClasses.Natural (D : HodgeClasses C) : Prop where
  /-- Changing labels preserves each Chern class. -/
  rename {n m : ℕ} (e : Fin n ≃ Fin m) (b : Fin 2) :
    C.rename 2 (Fin n) (Fin m) (stable n) (stable m) e (D.coefficient n b.succ) =
      (D.coefficient m b.succ : C.H 2 (Fin m))
  /-- The family with a new marking is the pullback from the original curve. -/
  forget (n : ℕ) (b : Fin 2) :
    C.rename 2 (Fin (n+1)) (Option (Fin n)) (stable _) (stable n).option (finSuccEquiv n)
      (D.coefficient (n+1) b.succ) = C.forget 2 (Fin n) (stable n) (D.coefficient n b.succ)

private theorem rename_coefficient {D : HodgeClasses C} (H : D.Natural) {n m : ℕ}
    (e : Fin n ≃ Fin m) (i : Fin 3) :
    C.rename 2 _ _ (stable n) (stable m) e (D.coefficient n i) =
      (D.coefficient m i : C.H 2 (Fin m)) := by
  refine Fin.cases ?_ (H.rename e) i
  exact map_one _

private theorem forget_coefficient {D : HodgeClasses C} (H : D.Natural) (n : ℕ) (i : Fin 3) :
    C.rename 2 _ _ (stable (n+1)) (stable n).option (finSuccEquiv n) (D.coefficient (n+1) i) =
      C.forget 2 (Fin n) (stable n) (D.coefficient n i) := by
  refine Fin.cases ?_ (H.forget n) i
  exact (map_one _).trans (map_one _).symm

/-- Relabeling ordered powers preserves Hodge moments, including repeated powers. -/
theorem moment_perm {D : HodgeClasses C} (H : D.Natural) (P : PsiClasses C)
    (I : StableCurveIntegration C) (i j : Fin 3) {p q : List ℕ} (h : p.Perm q) :
    moment D P I i j p = moment D P I i j q := by
  obtain ⟨e, he⟩ := markingEquiv_of_powers p.get q.get (by
    rw [Fin.univ_val_map, Fin.univ_val_map, List.ofFn_get, List.ofFn_get]
    exact Quot.sound h)
  have hget : (fun t ↦ p.get (e.symm t)) = q.get := by
    funext t
    simpa only [Equiv.apply_symm_apply] using (he (e.symm t)).symm
  unfold moment monomial
  rw [← I.integrate_rename 2 _ _ (stable p.length) (stable q.length) e]
  simp only [map_mul, rename_coefficient H, P.rename_monomial, hget]

/-- Move the first listed marking to the universal curve and pull both Hodge factors back. -/
theorem moment_cons {D : HodgeClasses C} (H : D.Natural) (P : PsiClasses C)
    (I : StableCurveIntegration C) (i j : Fin 3) (k : ℕ) (p : List ℕ) :
    moment D P I i j (k :: p) = I.integrate 2 (Option (Fin p.length)) (stable p.length).option
      (C.forget 2 (Fin p.length) (stable _) ((D.coefficient p.length i : C.H 2 (Fin p.length)) *
        (D.coefficient p.length j : C.H 2 (Fin p.length))) *
        P.monomial 2 _ (stable p.length).option (fun t ↦ t.elim k p.get)) := by
  have hget : (fun t ↦ (k :: p).get ((finSuccEquiv p.length).symm t)) =
      (fun t : Option (Fin p.length) ↦ t.elim k p.get) := by
    funext t
    cases t with
    | none => rw [finSuccEquiv_symm_none]; rfl
    | some t => rw [finSuccEquiv_symm_some]; rfl
  unfold moment monomial
  rw [← I.integrate_rename 2 _ _ (stable (k :: p).length) (stable p.length).option
    (finSuccEquiv p.length)]
  simp only [map_mul, P.rename_monomial, hget, List.length_cons, forget_coefficient H]

private theorem moment_lower (D : HodgeClasses C) (P : PsiClasses C) (I : StableCurveIntegration C)
    (i j : Fin 3) (p : List ℕ) (s : Fin p.length) :
    I.integrate 2 (Fin p.length) (stable _)
      (monomial D P i j (Function.update p.get s (p.get s - 1))) =
      moment D P I i j (lower p s) := by
  have bridge (n : ℕ) (d : Fin n → ℕ) (q : List ℕ) (h : n = q.length)
      (hd : ∀ t, d t = q.get (Fin.cast h t)) :
      I.integrate 2 (Fin n) (stable _) (monomial D P i j d) = moment D P I i j q := by
    subst n
    exact congrArg (fun v ↦ I.integrate 2 _ (stable _) (monomial D P i j v)) (funext hd)
  apply bridge _ _ _ (by simp only [lower, List.length_set])
  intro t
  by_cases ht : t = s
  · subst t
    simp only [lower, Function.update_self, List.get_eq_getElem, Fin.val_cast,
      List.getElem_set_self]
  · simp only [lower, Function.update_of_ne ht, List.get_eq_getElem, Fin.val_cast,
      List.getElem_set_ne (show s.val ≠ t.val from fun e ↦ ht (Fin.ext e.symm))]

variable {D : HodgeClasses C} (H : D.Natural) {I : StableCurveIntegration C}
    (U : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (T : TailForgetCompatible C)
include H U F N K hK T

/-- Forgetting the first marking gives one lower-power moment for each positive surviving mark. -/
theorem moment_string (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (i j : Fin 3) (p : List ℕ) :
    moment D P I i j (0 :: p) =
      ∑ s : Fin p.length, if 0 < p.get s then moment D P I i j (lower p s) else 0 := by
  rw [moment_cons H, string_integral U F N P K hK T vol]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : p.get s = 0
  · simp only [h, ite_true, lt_irrefl, ite_false]
  · rw [if_neg h, if_pos (Nat.pos_of_ne_zero h)]
    exact moment_lower D P I i j p s

omit H in
/-- The universal-curve square propagates the unmarked κ₀ normalization to every ordered arity. -/
theorem genus_two_kappa_zero (Q : ForgetfulSquareCompatibility U F)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2) (n : ℕ) :
    P.kappa U 2 (Fin n) (stable n) 0 = ((2+n : ℕ) : C.H 2 (Fin n)) := by
  induction n with
  | zero => simpa only [Nat.add_zero, Nat.cast_ofNat] using base
  | succ n ih =>
    apply (C.rename 2 (Fin (n+1)) (Option (Fin n)) (stable _) (stable n).option
      (finSuccEquiv n)).injective
    rw [P.kappa_rename, map_natCast]
    have hrec := Q.forget_kappa N P K hK T 2 (Fin n) (stable n) 0
    rw [ih, map_natCast, pow_zero] at hrec
    simpa only [Nat.add_succ, Nat.cast_succ] using (eq_add_of_sub_eq hrec.symm)

/-- Forgetting a first-power mark gives the genus-two dilaton multiplier. -/
theorem moment_dilaton (Q : ForgetfulSquareCompatibility U F)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2) (i j : Fin 3) (p : List ℕ) :
    moment D P I i j (1 :: p) = ((2+p.length : ℕ) : ℚ) * moment D P I i j p := by
  rw [moment_cons H]
  have hm : P.monomial 2 (Option (Fin p.length)) (stable p.length).option
      (fun t ↦ t.elim 1 p.get) = P.psi 2 _ (stable p.length).option none *
      P.monomial 2 _ (stable p.length).option (fun t ↦ t.elim 0 p.get) := by
    simp only [PsiClasses.monomial, Fintype.prod_option, Option.elim_none, Option.elim_some,
      pow_one, pow_zero, one_mul]
  rw [hm, ← mul_assoc, dilaton_integral U F N P K hK T,
    genus_two_kappa_zero U F N P K hK T Q base]
  rw [mul_comm _ ((2+p.length : ℕ) : C.H 2 (Fin p.length)), ← nsmul_eq_mul, map_nsmul,
    nsmul_eq_mul]
  rfl

/-- The numerical Hodge recurrences follow from the source-curve maps and two normalizations. -/
theorem moment_recurrences (Q : ForgetfulSquareCompatibility U F)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2) (i j : Fin 3) :
    Recurrences i j (moment D P I i j) where
  degree := moment_off_degree D P I i j
  relabel := moment_perm H P I i j
  string := moment_string H U F N P K hK T vol i j
  dilaton := moment_dilaton H U F N P K hK T Q base i j

/-- The eight reduced moments determine the integral of the product of the two Hodge factors,
marked cotangent powers and flag inverses, under the source-curve map laws. -/
theorem integral_from_geometry (Q : ForgetfulSquareCompatibility U F)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2) (seed : ↥seeds → ℚ)
    (hseed : ∀ (i j : Fin 3), i ≤ j → ∀ p (hk : ((i : ℕ), (j : ℕ), p) ∈ seeds),
      seed ⟨_, hk⟩ = moment D P I i j p) {L : Type*} [Field L] [CharZero L]
    {f : ℕ} (m : List ℕ) (u v : L) (flag : Fin f → L) :
    integrate I _ (integrand D P m u v flag) = GenusTwoLocalizationVertex.reduced seed m u v flag :=
  (congrArg (integrate I _) (expansion_eq_product D P m u v flag).symm).trans
    (integrate_eq_reduced D P I seed
      (fun i j _ ↦ moment_recurrences H U F N P K hK T Q vol base i j) hseed m u v flag)

end AxiomaticGW.GKM.GenusTwoLocalizationClass
