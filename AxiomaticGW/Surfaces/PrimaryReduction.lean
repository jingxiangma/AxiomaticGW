/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Queries
public import AxiomaticGW.GW.Descendants.FullDivisor
public import Mathlib.Data.Multiset.Fintype

/-!
# Primary surface reduction at nonzero curve class

String and divisor equations remove every primary insertion except point
classes. The remaining invariant uses the existing numerical extension, so
removal of divisors may cross into curve-unstable arities without discarding
positive-degree values. Intersection coefficients retain the full curve class
and the negative self-intersection of an exceptional divisor.

The divisor pairing must explicitly agree with the surface intersection form.
This compatibility is geometric input; the reduction itself is proved from
the existing string and divisor laws. Degree-zero exceptions are not removed.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceBasisLabel

/-- Contribution of one primary insertion after string/divisor reduction.
Point insertions are retained separately and contribute a factor of one. -/
def primaryFactor {X : SurfaceTarget} (beta : X.Curve) : SurfaceBasisLabel X → ℚ
  | unit => 0
  | hyperplane => X.divisorIntersections beta 0
  | exceptional i => X.divisorIntersections beta i.succ
  | point => 1

end SurfaceBasisLabel

namespace SurfaceTheoryIdentification

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}

/-- Transport a surface divisor into the identified theory's degree-one part. -/
def divisor (T : SurfaceTheoryIdentification X Omega) (d : X.Divisor) :
    Omega.graded.degree 1 :=
  ⟨d.val, by rw [T.degree_eq]; exact d.property⟩

/-- Identification of the divisor law's coefficients with actual curve
intersections. No numerical GW recurrence is included in this property. -/
def DivisorPairingCompatible (T : SurfaceTheoryIdentification X Omega)
    {I : StableCurveIntegration C} {F : ForgetfulPushforward C I}
    (A : GWDivisorAxiom Omega F) : Prop :=
  ∀ (d : X.Divisor) (beta : X.Curve),
    A.divisorPairing (T.divisor d) beta = X.divisorPairing d beta

end SurfaceTheoryIdentification

namespace SurfacePrimary

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- A multiset of primary labels evaluated with all occurrences retained. -/
noncomputable def eval (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  U.invariant g m beta (fun _ ↦ 0) (fun s ↦ (s : SurfaceBasisLabel X).value)

/-- Primary invariants with a fixed number of point insertions, at every arity. -/
noncomputable def pointInvariant (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (n : ℕ) : ℚ :=
  U.invariant g (Fin n) beta (fun _ ↦ 0)
    (fun _ ↦ SurfaceCohomology.point X.blowups)

/-- Relabelling primary insertions transports just their states. -/
theorem invariant_relabel (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (S T : Type) [Fintype S] [Fintype T]
    (e : S ≃ T) (a : S → SurfaceCohomology X.blowups) :
    U.invariant g S beta (fun _ ↦ 0) a =
      U.invariant g T beta (fun _ ↦ 0) (fun t ↦ a (e.symm t)) := by
  have h := congrArg (fun f ↦ f (fun t ↦ a (e.symm t)))
    (U.invariant_relabel g S T e beta (fun _ ↦ 0))
  simpa only [MultilinearMap.domDomCongr_apply, Equiv.symm_apply_apply,
    U.invariantMap_apply] using h

/-- Mapping insertion data to labels preserves all occurrences. -/
theorem eval_map (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) {α : Type} [DecidableEq α]
    (m : Multiset α) (a : α → SurfaceBasisLabel X) :
    eval U g beta (m.map a) =
      U.invariant g m beta (fun _ ↦ 0) (fun s ↦ (a (s : α)).value) := by
  rw [eval, invariant_relabel U g beta _ _ (m.mapEquiv a).symm]
  congr 1
  funext s
  rw [Equiv.symm_symm, Multiset.mapEquiv_apply]

/-- Expose one occurrence as the distinguished input of the string/divisor laws. -/
theorem eval_cons (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X)) :
    eval U g beta (b ::ₘ m) = U.invariant g (Option m) beta (fun _ ↦ 0)
      (fun | none => b.value | some s => (s : SurfaceBasisLabel X).value) := by
  rw [eval, invariant_relabel U g beta _ _ Multiset.consEquiv]
  congr 1
  funext s
  cases s <;> rfl

/-- A non-point primary insertion is removed by the existing string/divisor
laws. Nonzero curve degree is essential for the exceptional terms to vanish. -/
theorem eval_cons_of_ne_point (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (g : ℕ) (beta : X.Curve) (hbeta : beta ≠ 0)
    (b : SurfaceBasisLabel X) (hb : b ≠ .point)
    (m : Multiset (SurfaceBasisLabel X)) :
    eval U g beta (b ::ₘ m) = b.primaryFactor beta * eval U g beta m := by
  classical
  rw [eval_cons]
  cases b with
  | unit =>
      have h := U.global_string S g m beta (fun _ ↦ 0)
        (fun s ↦ (s : SurfaceBasisLabel X).value)
      rw [stringCorrection_eq_zero_of_ne_zero _ _ _ _ _ _ hbeta] at h
      simp only [T.unit_eq, SurfaceBasisLabel.value, SurfaceBasisLabel.primaryFactor,
        ite_true, Finset.sum_const_zero, add_zero, zero_mul] at h ⊢
      convert! h using 1
      congr 1 <;> funext x <;> cases x <;> rfl
  | hyperplane =>
      have h := H.global_divisor_of_ne_zero g m beta (fun _ ↦ 0)
        (fun s ↦ (s : SurfaceBasisLabel X).value)
        (T.divisor (SurfaceCohomology.hyperplaneDivisor X.blowups)) hbeta
      rw [hpair, SurfaceTarget.divisorPairing_hyperplane] at h
      simp only [SurfaceTheoryIdentification.divisor, SurfaceCohomology.hyperplaneDivisor,
        SurfaceBasisLabel.value, SurfaceBasisLabel.primaryFactor, eval,
        ite_true, Finset.sum_const_zero, add_zero] at h ⊢
      convert! h using 1
      congr 1 <;> funext x <;> cases x <;> rfl
  | exceptional i =>
      have h := H.global_divisor_of_ne_zero g m beta (fun _ ↦ 0)
        (fun s ↦ (s : SurfaceBasisLabel X).value)
        (T.divisor (SurfaceCohomology.exceptionalDivisor X.blowups i)) hbeta
      rw [hpair, SurfaceTarget.divisorPairing_exceptional] at h
      simp only [SurfaceTheoryIdentification.divisor, SurfaceCohomology.exceptionalDivisor,
        SurfaceBasisLabel.value, SurfaceBasisLabel.primaryFactor, eval,
        ite_true, Finset.sum_const_zero, add_zero] at h ⊢
      convert! h using 1
      congr 1 <;> funext x <;> cases x <;> rfl
  | point => exact (hb rfl).elim

/-- When all labels are points, only their number matters. -/
theorem eval_eq_pointInvariant (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (m : Multiset (SurfaceBasisLabel X))
    (hm : ∀ b ∈ m, b = .point) :
    eval U g beta m = pointInvariant U g beta m.card := by
  classical
  rw [eval, invariant_relabel U g beta _ _
    (Fintype.equivFinOfCardEq (Multiset.card_coe m))]
  unfold pointInvariant
  congr 1
  funext s
  rw [hm _ Multiset.coe_mem]
  rfl

/-- Complete primary reduction at nonzero curve class. This includes any
number of repeated divisors, units, and points, in every genus and arity. -/
theorem eval_reduced (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (g : ℕ) (beta : X.Curve) (hbeta : beta ≠ 0)
    (m : Multiset (SurfaceBasisLabel X)) :
    eval U g beta m = (m.map (SurfaceBasisLabel.primaryFactor beta)).prod *
      pointInvariant U g beta (m.count .point) := by
  classical
  induction m using Multiset.strongInductionOn with
  | ih m ih =>
      by_cases hp : ∀ b ∈ m, b = .point
      · have hc : m.count .point = m.card :=
          Multiset.count_eq_card.mpr (fun b hb ↦ (hp b hb).symm)
        have hf : (m.map (SurfaceBasisLabel.primaryFactor beta)).prod = 1 := by
          rw [Multiset.eq_replicate_of_mem hp, Multiset.map_replicate,
            SurfaceBasisLabel.primaryFactor, Multiset.prod_replicate, one_pow]
        rw [hc, hf, one_mul]
        exact eval_eq_pointInvariant U g beta m hp
      · obtain ⟨b, hb⟩ := not_forall.mp hp
        obtain ⟨hb, hbp⟩ := Classical.not_imp.mp hb
        obtain ⟨m', rfl⟩ := Multiset.exists_cons_of_mem hb
        rw [eval_cons_of_ne_point U T S H hpair g beta hbeta b hbp,
          ih m' (Multiset.lt_cons_self m' b)]
        rw [Multiset.map_cons, Multiset.prod_cons,
          Multiset.count_cons_of_ne (Ne.symm hbp), mul_assoc]

/-- The residual point invariant vanishes outside the surface virtual
dimension, including curve-unstable arities. -/
theorem pointInvariant_eq_zero_of_dimension_ne
    (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
    (g : ℕ) (beta : X.Curve) (n : ℕ)
    (hne : (n : ℤ) ≠ X.c1Degree beta + (g : ℤ) - 1) :
    pointInvariant U g beta n = 0 := by
  apply U.invariant_eq_zero_of_degree_ne g (Fin n) beta (fun _ ↦ 0)
    (fun _ ↦ 2) (fun _ ↦ SurfaceCohomology.point X.blowups)
  · intro _
    rw [T.degree_eq]
    exact SurfaceCohomology.point_mem_degree_two _
  · intro h
    apply hne
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_zero, Nat.cast_zero, add_zero, Nat.cast_mul, Nat.cast_ofNat,
      T.dimension_eq, T.c1Degree_eq, GWVirtualDimension] at h
    omega

end SurfacePrimary

namespace SurfaceQuery

/-- The residual primary point query. Its full curve class and every point
insertion are retained, even when its curve arity is unstable. -/
def points (X : SurfaceTarget) (g : ℕ) (beta : X.Curve) (n : ℕ) : SurfaceQuery X :=
  ⟨g, beta, List.replicate n ⟨.point, 0⟩⟩

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

theorem eval_points (U : UnstableDescendantConventions M I)
    (g : ℕ) (beta : X.Curve) (n : ℕ) :
    (points X g beta n).eval U = SurfacePrimary.pointInvariant U g beta n := by
  simp only [eval, points, List.get_eq_getElem,
    List.getElem_replicate, SurfaceBasisLabel.value, SurfacePrimary.pointInvariant]
  exact SurfacePrimary.invariant_relabel U g beta _ _
    (finCongr (show (List.replicate n (⟨.point, 0⟩ : SurfaceInsertion X)).length = n
      from List.length_replicate)) _

end SurfaceQuery

end AxiomaticGW
