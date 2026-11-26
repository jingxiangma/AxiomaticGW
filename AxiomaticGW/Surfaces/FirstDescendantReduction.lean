/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.DescendantDivisor
public import AxiomaticGW.Coefficients.RationalTerms

/-!
# First descendants and the primary/one-descendant surface families

In genus at least two every marking type is stable. String, dilaton and
divisor therefore reduce a single cotangent power and arbitrary primary
insertions to point primaries and one descendant followed by points, even
at curve class zero. The divisor correction uses the classical surface
product, including the negative exceptional squares. No value for the
remaining genus-two primary invariant at class zero is presumed.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceBasisLabel
/-- At curve class zero every primary non-point has zero divisor/string factor. -/
theorem primaryFactor_zero_of_ne_point {X : SurfaceTarget} (b : SurfaceBasisLabel X)
    (hb : b ≠ .point) : b.primaryFactor (0 : X.Curve) = 0 := by
  cases b with
  | unit => rfl
  | hyperplane =>
    change (X.divisorIntersections 0 0 : ℚ) = 0
    rw [← SurfaceTarget.divisorPairing_hyperplane, map_zero]
  | exceptional i =>
    change (X.divisorIntersections 0 i.succ : ℚ) = 0
    rw [← SurfaceTarget.divisorPairing_exceptional, map_zero]
  | point => exact (hb rfl).elim
end SurfaceBasisLabel

namespace SurfacePrimary
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- In genus at least two, removing a primary non-point has no exceptional
arity contribution, including when the curve class is zero. -/
theorem eval_cons_of_two_le (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A) (g : ℕ) (hg : 2 ≤ g) (beta : X.Curve)
    (b : SurfaceBasisLabel X) (hb : b ≠ .point) (m : Multiset (SurfaceBasisLabel X)) :
    eval U g beta (b ::ₘ m) = b.primaryFactor beta * eval U g beta m := by
  by_cases hbeta : beta = 0
  · subst beta
    cases b with
    | unit =>
      rw [eval_unit_zero U T S, if_neg (by omega)]
      exact (zero_mul _).symm
    | hyperplane =>
      rw [eval_divisor_zero_of_stable U T H g .hyperplane rfl m (by
        unfold StableArity; omega)]
      rw [SurfaceBasisLabel.primaryFactor_zero_of_ne_point _ hb, zero_mul]
    | exceptional i =>
      rw [eval_divisor_zero_of_stable U T H g (.exceptional i) rfl m (by
        unfold StableArity; omega)]
      rw [SurfaceBasisLabel.primaryFactor_zero_of_ne_point _ hb, zero_mul]
    | point => exact (hb rfl).elim
  · exact eval_cons_of_ne_point U T S H hpair g beta hbeta b hb m

/-- Primary reduction extends to degree zero once all base arities are stable. -/
theorem eval_reduced_of_two_le (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A) (g : ℕ) (hg : 2 ≤ g) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) :
    eval U g beta m = (m.map (SurfaceBasisLabel.primaryFactor beta)).prod *
      pointInvariant U g beta (m.count .point) := by
  by_cases hbeta : beta = 0
  · subst beta
    by_cases hp : ∀ b ∈ m, b = .point
    · have hc : m.count .point = m.card :=
        Multiset.count_eq_card.mpr (fun b hb ↦ (hp b hb).symm)
      rw [eval_eq_pointInvariant U g 0 m hp, hc, Multiset.eq_replicate_of_mem hp]
      simp only [Multiset.map_replicate, Multiset.prod_replicate,
        SurfaceBasisLabel.primaryFactor, one_pow, one_mul]
    · obtain ⟨b, hb⟩ := not_forall.mp hp
      obtain ⟨hb, hbp⟩ := Classical.not_imp.mp hb
      obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem hb
      have hz := b.primaryFactor_zero_of_ne_point hbp
      rw [eval_cons_of_two_le U T S H hpair g hg 0 b hbp, Multiset.map_cons,
        Multiset.prod_cons, hz, zero_mul, zero_mul, zero_mul]
  · exact eval_reduced U T S H hpair g beta hbeta m

end SurfacePrimary

namespace SurfaceFirstDescendant
variable {X : SurfaceTarget}

/-- All primary insertions contribute their divisor factors except retained points. -/
def primaryCoefficient (beta : X.Curve) (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  (m.map (SurfaceBasisLabel.primaryFactor beta)).prod

/-- The self-intersection coefficient of a divisor label; other labels contribute zero. -/
def divisorSquare : SurfaceBasisLabel X → ℚ
  | .hyperplane => 1
  | .exceptional _ => -1
  | .unit | .point => 0

/-- Different basis divisors are orthogonal. -/
def divisorIntersection (b d : SurfaceBasisLabel X) : ℚ :=
  if d = b then divisorSquare b else 0

/-- Only primary copies of the descendant's divisor can yield the point correction. -/
def correctionCoefficient (beta : X.Curve) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  divisorSquare b * (m.count b : ℚ) * primaryCoefficient beta (m.erase b)

/-- The remaining first-descendant family uses only primary point insertions. -/
def query (g : ℕ) (beta : X.Curve) (b : SurfaceBasisLabel X) (n : ℕ) : SurfaceQuery X :=
  ⟨g, beta, ⟨b, 1⟩ :: List.replicate n ⟨.point, 0⟩⟩

/-- Discard a term only by its exact integer virtual-dimension check. -/
def dimensionTerms (q : SurfaceQuery X) : RationalTerms (SurfaceQuery X) :=
  if q.DimensionCompatible then RationalTerms.term 1 {q} else 0

/-- The primary reduction records the complete residual point request. -/
def primaryTerms (g : ℕ) (beta : X.Curve) (m : Multiset (SurfaceBasisLabel X)) :
    RationalTerms (SurfaceQuery X) :=
  RationalTerms.scale (primaryCoefficient beta m)
    (dimensionTerms (SurfaceQuery.points X g beta (m.count .point)))

/-- Executable string, dilaton and divisor normalization, without dividing
by any intersection coefficient or introducing a numerical seed. -/
def terms (g : ℕ) (beta : X.Curve) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X)) : RationalTerms (SurfaceQuery X) :=
  if .unit ∈ m then primaryTerms g beta (b ::ₘ m.erase .unit)
  else if b = .unit then
    RationalTerms.scale (((2 * g + m.card : ℕ) : ℚ) - 2) (primaryTerms g beta m)
  else
    RationalTerms.scale (primaryCoefficient beta m)
      (dimensionTerms (query g beta b (m.count .point))) +
    RationalTerms.scale (correctionCoefficient beta b m)
      (dimensionTerms (SurfaceQuery.points X g beta (m.count .point + 1)))

theorem primaryCoefficient_cons (beta : X.Curve) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X)) :
    primaryCoefficient beta (b ::ₘ m) = b.primaryFactor beta * primaryCoefficient beta m := by
  simp only [primaryCoefficient, Multiset.map_cons, Multiset.prod_cons]

/-- This identity also holds at zero divisor pairing; it uses no division. -/
theorem correctionCoefficient_cons (beta : X.Curve) (b d : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X)) :
    correctionCoefficient beta b (d ::ₘ m) =
      d.primaryFactor beta * correctionCoefficient beta b m +
        divisorIntersection b d * primaryCoefficient beta m := by
  by_cases hdb : d = b
  · subst d
    simp only [correctionCoefficient, Multiset.count_cons_self, Multiset.erase_cons_head,
      Nat.cast_add, Nat.cast_one, divisorIntersection, ite_true]
    by_cases hb : b ∈ m
    · have hm := Multiset.cons_erase hb
      have hp := congrArg (primaryCoefficient beta) hm
      rw [primaryCoefficient_cons] at hp
      rw [← hp]
      ring
    · rw [Multiset.count_eq_zero_of_notMem hb]
      simp only [Nat.cast_zero, zero_add, mul_one, mul_zero, zero_mul, zero_add]
  · simp only [correctionCoefficient, Multiset.count_cons_of_ne (Ne.symm hdb),
      Multiset.erase_cons_tail m hdb, primaryCoefficient_cons, divisorIntersection, if_neg hdb]
    ring

/-- Multiplying a divisor by a non-unit basis state gives the signed point term. -/
theorem value_mul_of_divisor (b d : SurfaceBasisLabel X)
    (hb : b ≠ .unit) (hd : d.codimension = 1) :
    d.value * b.value =
      divisorIntersection b d • (SurfaceBasisLabel.point : SurfaceBasisLabel X).value := by
  cases d <;> cases b <;> (try exact (hb rfl).elim) <;>
    norm_num only [SurfaceBasisLabel.codimension] at hd
  all_goals
    simp only [SurfaceBasisLabel.value, divisorIntersection, divisorSquare,
      SurfaceBasisLabel.exceptional.injEq, reduceCtorEq, ite_true, ite_false,
      SurfaceCohomology.hyperplane_mul_hyperplane, SurfaceCohomology.hyperplane_mul_exceptional,
      SurfaceCohomology.exceptional_mul_exceptional, one_smul, zero_smul]
  · rw [mul_comm, SurfaceCohomology.point_mul_hyperplane]
  · rw [mul_comm, SurfaceCohomology.hyperplane_mul_exceptional]
  · split_ifs <;> simp only [neg_smul, one_smul, zero_smul]
  · rw [mul_comm, SurfaceCohomology.point_mul_exceptional]

variable {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- One labelled descendant and a multiset of primary occurrences. -/
noncomputable def eval (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  U.invariant g (Option m) beta (fun | none => 1 | some _ => 0)
    (fun | none => b.value | some s => (s : SurfaceBasisLabel X).value)

/-- Relabelling transports descendant powers together with states. -/
theorem invariant_relabel (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (S T : Type) [Fintype S] [Fintype T]
    (e : S ≃ T) (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) :
    U.invariant g S beta k a =
      U.invariant g T beta (fun t ↦ k (e.symm t)) (fun t ↦ a (e.symm t)) := by
  have h := congrArg (fun f ↦ f (fun t ↦ a (e.symm t)))
    (U.invariant_relabel g S T e beta k)
  simpa only [MultilinearMap.domDomCongr_apply, Equiv.symm_apply_apply,
    U.invariantMap_apply] using h

/-- Reindex the primary occurrences while retaining the descendant marking. -/
theorem eval_map (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (b : SurfaceBasisLabel X) {α : Type} [DecidableEq α]
    (m : Multiset α) (a : α → SurfaceBasisLabel X) :
    eval U g beta b (m.map a) = U.invariant g (Option m) beta
      (fun | none => 1 | some _ => 0)
      (fun | none => b.value | some s => (a (s : α)).value) := by
  rw [eval, invariant_relabel U g beta _ _ (Equiv.optionCongr (m.mapEquiv a).symm)]
  congr 1
  · funext s; cases s <;> rfl
  · funext s
    cases s with
    | none => rfl
    | some s =>
      change ((m.mapEquiv a) s : SurfaceBasisLabel X).value = (a (s : α)).value
      rw [Multiset.mapEquiv_apply]

/-- Expose a primary occurrence as the new marking while keeping the
cotangent power on its original descendant occurrence. -/
theorem eval_cons (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (b d : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X)) :
    eval U g beta b (d ::ₘ m) = U.invariant g (Option (Option m)) beta
      (fun | none => 0 | some none => 1 | some (some _) => 0)
      (fun | none => d.value | some none => b.value
           | some (some s) => (s : SurfaceBasisLabel X).value) := by
  classical
  rw [eval, invariant_relabel U g beta _ _
    ((Equiv.optionCongr Multiset.consEquiv).trans (Equiv.swap none (some none)))]
  congr 1 <;> funext s <;> rcases s with _ | (_ | s) <;>
    simp only [Equiv.symm_trans_apply, Equiv.symm_swap,
      Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne,
      Option.some_ne_none, ne_eq, Option.some.injEq, not_false_eq_true,
      ← Equiv.optionCongr_symm, Equiv.optionCongr_apply, Option.map_none, Option.map_some,
      Multiset.consEquiv_symm_none, Multiset.consEquiv_symm_some]

/-- A primary unit removes the unique cotangent power by the string equation. -/
theorem eval_unit_primary (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    (g : ℕ) (hg : 2 ≤ g) (beta : X.Curve) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X)) :
    eval U g beta b (.unit ::ₘ m) = SurfacePrimary.eval U g beta (b ::ₘ m) := by
  classical
  rw [eval_cons, SurfacePrimary.eval_cons]
  have h := U.global_string laws g (Option m) beta
    (fun | none => 1 | some _ => 0)
    (fun | none => b.value | some s => (s : SurfaceBasisLabel X).value)
  rw [stringCorrection_eq_zero_of_stable _ _ _ _ _ _ (by unfold StableArity; omega)] at h
  simp only [T.unit_eq, Fintype.sum_option, one_ne_zero, if_false, ite_true,
    Finset.sum_const_zero, add_zero] at h
  convert! h using 1
  · congr 1 <;> funext s <;> rcases s with _ | (_ | s) <;> rfl
  · congr 1
    funext s
    cases s <;> simp only [lowerPower, Function.update_self,
      Function.update_of_ne (Option.some_ne_none _), Nat.sub_self]

/-- A descendant unit is removed by dilaton, with all multiplicities retained. -/
theorem eval_unit_descendant (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    (g : ℕ) (hg : 2 ≤ g) (beta : X.Curve) (m : Multiset (SurfaceBasisLabel X)) :
    eval U g beta .unit m = (((2 * g + m.card : ℕ) : ℚ) - 2) *
      SurfacePrimary.eval U g beta m := by
  classical
  have h := U.global_dilaton laws g m beta (fun _ ↦ 0)
    (fun s ↦ (s : SurfaceBasisLabel X).value)
  rw [dilatonCorrection_eq_zero_of_stable _ _ _ _ (by unfold StableArity; omega)] at h
  simp only [T.unit_eq, dilatonCoefficient, Multiset.card_coe, add_zero] at h
  unfold eval SurfacePrimary.eval
  convert! h using 1
  congr 1 <;> funext s <;> cases s <;> rfl

/-- The one-descendant divisor correction is a point insertion with its
signed intersection coefficient. Both terms keep the complete curve class. -/
theorem eval_divisor_primary (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A) (g : ℕ) (hg : 2 ≤ g) (beta : X.Curve)
    (b d : SurfaceBasisLabel X) (hb : b ≠ .unit) (hd : d.codimension = 1)
    (m : Multiset (SurfaceBasisLabel X)) :
    eval U g beta b (d ::ₘ m) = d.primaryFactor beta * eval U g beta b m +
      divisorIntersection b d * SurfacePrimary.eval U g beta (.point ::ₘ m) := by
  classical
  let div : X.Divisor := ⟨d.value, by
    change d.value ∈ SurfaceCohomology.degree X.blowups 1
    rw [← hd]
    exact d.value_mem_degree⟩
  have hpair' : A.divisorPairing (T.divisor div) beta = d.primaryFactor beta := by
    rw [hpair]
    cases d with
    | unit => norm_num only [SurfaceBasisLabel.codimension] at hd
    | point => norm_num only [SurfaceBasisLabel.codimension] at hd
    | hyperplane => exact X.divisorPairing_hyperplane beta
    | exceptional i => exact X.divisorPairing_exceptional i beta
  let a : Option m → SurfaceCohomology X.blowups :=
    fun | none => b.value | some s => (s : SurfaceBasisLabel X).value
  have h := H.global_divisor g (Option m) beta (fun | none => 1 | some _ => 0) a
    (T.divisor div)
  rw [divisorCorrection_eq_zero_of_stable _ _ _ _ _ _ _ _ _
    (by unfold StableArity; omega), hpair'] at h
  simp only [Fintype.sum_option, one_ne_zero, if_false, ite_true,
    Finset.sum_const_zero, add_zero] at h
  have hk : lowerPower (fun | (none : Option m) => 1 | some _ => 0) none = 0 := by
    funext s
    cases s <;> simp only [lowerPower, Function.update_self,
      Function.update_of_ne (Option.some_ne_none _), Nat.sub_self, Pi.zero_apply]
  rw [hk, T.divisorAction_eq_mul U laws L] at h
  have hc : U.invariant g (Option m) beta 0
      (replaceInput a none (d.value * b.value)) =
      divisorIntersection b d * SurfacePrimary.eval U g beta (.point ::ₘ m) := by
    rw [value_mul_of_divisor b d hb hd, replaceInput, ← U.invariantMap_apply,
      MultilinearMap.map_update_smul, smul_eq_mul, U.invariantMap_apply,
      SurfacePrimary.eval_cons]
    congr 2
    funext s
    cases s <;> simp only [Function.update_self,
      Function.update_of_ne (Option.some_ne_none _), a]
  change _ = _ + U.invariant g (Option m) beta 0
    (replaceInput a none (d.value * b.value)) at h
  rw [hc] at h
  rw [eval_cons]
  convert! h using 1
  · congr 1 <;> funext s <;> rcases s with _ | (_ | s) <;> rfl

/-- The list query really has one descendant marking and exactly `n` primary points. -/
theorem eval_query (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (b : SurfaceBasisLabel X) (n : ℕ) :
    (query g beta b n).eval U = U.invariant g (Option (Fin n)) beta
      (fun | none => 1 | some _ => 0)
      (fun | none => b.value
           | some _ => (SurfaceBasisLabel.point : SurfaceBasisLabel X).value) := by
  let e : Fin (query g beta b n).insertions.length ≃ Option (Fin n) :=
    (finCongr (show (query g beta b n).insertions.length = n + 1
      by simp only [query, List.length_cons, List.length_replicate])).trans (finSuccEquiv n)
  have hn : (e.symm none).val = 0 := by
    change ((finSuccEquiv n).symm none).val = 0
    rw [finSuccEquiv_symm_none]
    rfl
  have hs (s : Fin n) : (e.symm (some s)).val = s.val + 1 := by
    change ((finSuccEquiv n).symm (some s)).val = s.val + 1
    rw [finSuccEquiv_symm_some]
    rfl
  refine (invariant_relabel U g beta _ _ e
    (fun i ↦ ((query g beta b n).insertions.get i).psi)
    (fun i ↦ ((query g beta b n).insertions.get i).label.value)).trans ?_
  congr 1 <;> funext s <;> cases s <;>
    simp only [List.get_eq_getElem, hn, hs] <;>
    simp only [query, List.getElem_cons_zero, List.getElem_cons_succ, List.getElem_replicate]

/-- Once every primary state is a point, only their number is relevant. -/
theorem eval_eq_query (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X)) (hm : ∀ d ∈ m, d = .point) :
    eval U g beta b m = (query g beta b m.card).eval U := by
  classical
  rw [eval, eval_query, invariant_relabel U g beta _ _
    (Equiv.optionCongr (Fintype.equivFinOfCardEq (Multiset.card_coe m)))]
  congr 1
  · funext s; cases s <;> rfl
  · funext s
    cases s with
    | none => rfl
    | some s =>
      change ((Fintype.equivFinOfCardEq (Multiset.card_coe m)).symm s :
        SurfaceBasisLabel X).value = SurfaceBasisLabel.point.value
      rw [hm _ Multiset.coe_mem]

/-- Removing arbitrary primary divisors leaves at most two canonical
invariants. The formula remains valid when a divisor pairing is zero. -/
theorem eval_reduced_of_no_units (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A) (g : ℕ) (hg : 2 ≤ g) (beta : X.Curve)
    (b : SurfaceBasisLabel X) (hb : b ≠ .unit) (m : Multiset (SurfaceBasisLabel X))
    (hm : .unit ∉ m) :
    eval U g beta b m = primaryCoefficient beta m *
      (query g beta b (m.count .point)).eval U + correctionCoefficient beta b m *
        SurfacePrimary.pointInvariant U g beta (m.count .point + 1) := by
  induction m using Multiset.strongInductionOn with
  | ih m ih =>
    by_cases hp : ∀ d ∈ m, d = .point
    · have hc : m.count .point = m.card :=
        Multiset.count_eq_card.mpr (fun d hd ↦ (hp d hd).symm)
      have hpcoef : primaryCoefficient beta m = 1 := by
        rw [primaryCoefficient, Multiset.eq_replicate_of_mem hp]
        simp only [Multiset.map_replicate, Multiset.prod_replicate,
          SurfaceBasisLabel.primaryFactor, one_pow]
      have hcc : correctionCoefficient beta b m = 0 := by
        by_cases hbp : b = .point
        · subst b
          simp only [correctionCoefficient, divisorSquare, zero_mul]
        · have hbm : b ∉ m := fun hmem ↦ hbp (hp b hmem)
          simp only [correctionCoefficient, Multiset.count_eq_zero_of_notMem hbm,
            Nat.cast_zero, mul_zero, zero_mul]
      rw [hpcoef, hcc, one_mul, zero_mul, add_zero, hc]
      exact eval_eq_query U g beta b m hp
    · obtain ⟨d, hd⟩ := not_forall.mp hp
      obtain ⟨hd, hdp⟩ := Classical.not_imp.mp hd
      have hdu : d ≠ .unit := fun heq ↦ hm (heq ▸ hd)
      have hdiv : d.codimension = 1 := by
        cases d <;> simp only [SurfaceBasisLabel.codimension] <;> contradiction
      obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem hd
      have hmu : .unit ∉ m := fun hu ↦ hm (Multiset.mem_cons_of_mem hu)
      rw [eval_divisor_primary U T laws H hpair g hg beta b d hb hdiv,
        ih m (Multiset.lt_cons_self m d) hmu,
        SurfacePrimary.eval_reduced_of_two_le U T laws H hpair g hg beta,
        primaryCoefficient_cons, correctionCoefficient_cons,
        Multiset.count_cons_of_ne (Ne.symm hdp), Multiset.count_cons_self]
      simp only [primaryCoefficient, Multiset.map_cons, Multiset.prod_cons,
        SurfaceBasisLabel.primaryFactor, one_mul]
      ring

/-- Dimension filtering preserves the actual stable-map value. -/
theorem eval_dimensionTerms (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (q : SurfaceQuery X) :
    RationalTerms.eval (SurfaceQuery.eval U) (dimensionTerms q) = q.eval U := by
  unfold dimensionTerms
  split_ifs with hd
  · simp only [RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton,
      Algebra.algebraMap_self_apply, one_mul]
  · rw [RationalTerms.eval_zero, q.eval_eq_zero_of_dimension_incompatible U T hd]

/-- The primary part is valid at all curve classes in genus at least two. -/
theorem eval_primaryTerms (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A) (g : ℕ) (hg : 2 ≤ g) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) :
    RationalTerms.eval (SurfaceQuery.eval U) (primaryTerms g beta m) =
      SurfacePrimary.eval U g beta m := by
  rw [primaryTerms, RationalTerms.eval_scale, eval_dimensionTerms U T, SurfaceQuery.eval_points,
    Algebra.algebraMap_self_apply, SurfacePrimary.eval_reduced_of_two_le U T laws H hpair g hg]
  rfl

/-- Soundness of the complete first-descendant normalization. Remaining
canonical invariants are outputs, not assumed values or extra axioms. -/
theorem eval_terms (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A) (g : ℕ) (hg : 2 ≤ g) (beta : X.Curve)
    (b : SurfaceBasisLabel X) (m : Multiset (SurfaceBasisLabel X)) :
    RationalTerms.eval (SurfaceQuery.eval U) (terms g beta b m) = eval U g beta b m := by
  unfold terms
  split_ifs with hu hb
  · rw [eval_primaryTerms U T laws H hpair g hg]
    have h := eval_unit_primary U T laws g hg beta b (m.erase .unit)
    rw [Multiset.cons_erase hu] at h
    exact h.symm
  · subst b
    rw [RationalTerms.eval_scale, Algebra.algebraMap_self_apply,
      eval_primaryTerms U T laws H hpair g hg, eval_unit_descendant U T laws g hg]
  · rw [RationalTerms.eval_add, RationalTerms.eval_scale, RationalTerms.eval_scale,
      eval_dimensionTerms U T, eval_dimensionTerms U T, Algebra.algebraMap_self_apply,
      Algebra.algebraMap_self_apply, SurfaceQuery.eval_points]
    exact (eval_reduced_of_no_units U T laws H hpair g hg beta b hb m hu).symm

end SurfaceFirstDescendant
end AxiomaticGW
