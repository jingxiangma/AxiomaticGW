/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoRemainder

/-!
# Primary factors of a first-power cotangent tail

Pulling back a single psi factor creates a rational tail carrying the old
insertion and the new point. The old main marking becomes the attaching node.
The formula below follows the actual label equivalences in that construction
and retains every class split, inverse-metric sign and binomial multiplicity.
The tail is the term that is subtracted in the signed pullback.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

/-- The new point is already on a cotangent tail. In line degree, the only
surviving node/old-label pairs are HH, HP and PH; HH needs one more point. -/
theorem sum_binomial_primary_plane_tail (f : ℕ → ℚ) (n : ℕ)
    (b c : SurfaceBasisLabel .plane) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * primaryScalar .plane (pointValue .plane) ![1] ij.2
        (Option.elim · b (fun t : Bool ↦ if t then .point else c)))) =
      match b, c with
      | .hyperplane, .hyperplane => (n : ℚ) * f (n - 1)
      | .hyperplane, .point | .point, .hyperplane => f n
      | _, _ => 0 := by
  rw [sum_binomial_primary_plane_one]
  cases b with
  | unit => rfl
  | exceptional i => exact Fin.elim0 i
  | hyperplane =>
    cases c with
    | unit => rfl
    | exceptional i => exact Fin.elim0 i
    | hyperplane =>
      change (n.choose 1 : ℚ) * f (n - 1) = _
      rw [Nat.choose_one_right]
    | point =>
      change (n.choose 0 : ℚ) * f (n - 0) = _
      rw [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul]
  | point =>
    cases c with
    | unit => rfl
    | exceptional i => exact Fin.elim0 i
    | hyperplane =>
      change (n.choose 0 : ℚ) * f (n - 0) = _
      rw [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul]
    | point => rfl

end AxiomaticGW.SurfaceGenusZero

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction GluingExpression

/-- A first-power correction has a primary main component and a primary
rational triple; its label and point multiplicities are the actual pullback's. -/
theorem remainderContraction_onePsi_tail {X : SurfaceTarget} (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (delta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    let z := CotangentTerm.tail h (Pi.single s 1) s
    remainderContraction X v main z.expression z.decoration z.labels
      delta n (Option.elim · .point a) =
      ∑ split ∈ X.splittings delta, ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
          (main ij.1 2 S h 0 inferInstance split.1 (Function.update a s b) *
            SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) split.2 ij.2
              (Option.elim · b.dual (fun t : Bool ↦ if t then .point else a s))) := by
  have hd : Function.update (Pi.single s 1 : S → ℕ) s
      ((Pi.single s 1 : S → ℕ) s - 1) = (0 : S → ℕ) := by
    funext t
    by_cases ht : t = s
    · subst t
      simp only [Function.update_self, Pi.single_eq_same, Nat.sub_self, Pi.zero_apply]
    · rw [Function.update_of_ne ht, Pi.single_eq_of_ne ht]
      rfl
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b (((Option.elim · SurfaceBasisLabel.point a) ∘
        PsiBoundaryExpansion.tailLabels s) ∘ Sum.inl)) ∘ (Equiv.optionSubtypeNe s).symm =
        Function.update a s b := by
    funext t
    by_cases ht : t = s
    · subst t
      simp only [Function.comp_apply, Equiv.optionSubtypeNe_symm_self,
        Option.elim_none, Function.update_self]
    · simp only [Function.comp_apply, Equiv.optionSubtypeNe_symm_of_ne ht,
        Option.elim_some, Function.update_of_ne ht, PsiBoundaryExpansion.tailLabels]
      rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((Option.elim · SurfaceBasisLabel.point a) ∘
        PsiBoundaryExpansion.tailLabels s) ∘ Sum.inr)) =
        (Option.elim · b (fun t : Bool ↦ if t then .point else a s)) := by
    funext t
    rcases t with _ | (_ | _) <;> rfl
  have hz : (fun _ : Option Bool ↦ (0 : ℕ)) = 0 := rfl
  dsimp only
  simp only [CotangentTerm.tail, CotangentTerm.relabel, CotangentTerm.separating,
    CotangentTerm.fundamental, remainderContraction, ite_true, hd,
    primaryPointVertex_eq, GluingExpression.pointContraction,
    hz, vertex_primary_genusZero_eq, hl, hr]

/-- For a one-degree plane remainder, the new rational tail must carry the
line. All placement and node sums reduce to these explicit primary components.
This is the positive tail term; the universal-curve formula subtracts it. -/
theorem remainderContraction_onePsi_plane_line (v : Variable .plane)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (n : ℕ) (a : S → SurfaceBasisLabel .plane) :
    let z := CotangentTerm.tail h (Pi.single s 1) s
    let main := remainderVertex .plane v (planeCoefficientVertex v)
    let f := fun m b ↦ main m 2 S h 0 inferInstance 0 (Function.update a s b)
    remainderContraction .plane v main z.expression z.decoration z.labels
      ![1] n (Option.elim · .point a) =
      match a s with
      | .hyperplane => (n : ℚ) * f (n - 1) .hyperplane
      | .point => f n .hyperplane
      | _ => 0 := by
  dsimp only
  rw [remainderContraction_onePsi_tail, SurfaceTarget.sum_plane_splittings_one]
  have hz (m : ℕ) (b : SurfaceBasisLabel .plane) :
      remainderVertex .plane v (planeCoefficientVertex v) m 2 S h 0 inferInstance
        ![1] (Function.update a s b) = 0 := by
    rw [remainderVertex_plane_primary, if_neg (by decide)]
  have hsum (b : SurfaceBasisLabel .plane) :=
    SurfaceGenusZero.sum_binomial_primary_plane_tail
      (fun m ↦ remainderVertex .plane v (planeCoefficientVertex v) m 2 S h 0 inferInstance
        0 (Function.update a s b)) n b.dual (a s)
  have hu (m : ℕ) :
      remainderVertex .plane v (planeCoefficientVertex v) m 2 S h 0 inferInstance
        0 (Function.update a s .unit) = 0 := by
    rw [remainderVertex_eq _ _ _ (planeCoefficientVertex_eq v),
      vertex_primary_genusTwo_unit_zero]
  simp only [hz, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, hsum]
  rw [SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    one_mul, Fin.sum_univ_zero, add_zero]
  cases hs : a s with
  | unit => exact zero_add 0
  | exceptional i => exact Fin.elim0 i
  | hyperplane => exact (congrArg (· + _) (hu n)).trans (zero_add _)
  | point => exact zero_add _

/-- One primary point preserves the old psi on the main component and subtracts
its actual rational tail. This identity retains every effective remainder. -/
theorem remainderVertex_onePsi_plane_step (v : Variable .plane)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (n : ℕ) (a : S → SurfaceBasisLabel .plane) (delta : SurfaceTarget.plane.Curve) :
    let main := remainderVertex .plane v (planeCoefficientVertex v)
    let z := CotangentTerm.tail h (Pi.single s 1) s
    main (n + 1) 2 S h (Pi.single s 1) inferInstance delta a =
      main n 2 (Option S) h.option (Pi.single (some s) 1) inferInstance delta
        (Option.elim · .point a) -
      remainderContraction .plane v main z.expression z.decoration z.labels
        delta n (Option.elim · .point a) := by
  let main := remainderVertex .plane v (planeCoefficientVertex v)
  let z := CotangentTerm.tail h (Pi.single s 1) s
  have ht := (remainderContraction_eq .plane v main z.expression le_rfl rfl
    z.decoration z.labels delta n (Option.elim · .point a)
    (fun m _ T _ hT k lT epsilon b ↦
      remainderVertex_eq .plane v _ (planeCoefficientVertex_eq v) m T hT k lT epsilon b)).symm
  have hf : Finset.univ.filter (fun t ↦ (Pi.single s 1 : S → ℕ) t ≠ 0) = {s} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases ht : t = s
    · subst t
      simp only [Pi.single_eq_same]
      decide
    · simp only [Pi.single_eq_of_ne ht, ne_eq, not_true_eq_false, ht]
  have hk : (fun t : Option S ↦ t.elim 0 (Pi.single s 1)) = Pi.single (some s) 1 := by
    funext t
    cases t with
    | none => simp only [Option.elim_none, Pi.single_eq_of_ne
        (show (none : Option S) ≠ some s from by intro he; cases he)]
    | some t =>
      by_cases ht : t = s
      · subst t
        simp only [Option.elim_some, Pi.single_eq_same]
      · simp only [Option.elim_some, Pi.single_eq_of_ne ht,
          Pi.single_eq_of_ne (fun he ↦ ht (Option.some.inj he))]
  dsimp only
  rw [remainderVertex_eq _ _ _ (planeCoefficientVertex_eq v), SurfacePointPullback.vertex_succ]
  simp only [GluingExpression.addCotangentMarking, hf, Finset.singleton_val,
    Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton,
    Int.cast_one, Int.cast_neg, one_mul, neg_one_mul]
  rw [← sub_eq_add_neg]
  change SurfacePointPullback.vertex .plane (coefficientVertex .plane v) n 2 (Option S)
    h.option (fun t ↦ t.elim 0 (Pi.single s 1)) inferInstance
      (SurfaceGenusZero.variableCurve v + delta) (Option.elim · .point a) -
    z.expression.pointContraction .plane (SurfacePointPullback.vertex .plane
      (coefficientVertex .plane v)) z.decoration z.labels
      (SurfaceGenusZero.variableCurve v + delta) n (Option.elim · .point a) = _
  rw [hk, ht, ← remainderVertex_eq _ _ _ (planeCoefficientVertex_eq v)]

/-- One more point keeps the old psi on the main component and subtracts the
proved line-tail contribution. Both terms are coefficients of the original pullback. -/
theorem remainderVertex_onePsi_plane_succ (v : Variable .plane)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (n : ℕ) (a : S → SurfaceBasisLabel .plane) :
    let main := remainderVertex .plane v (planeCoefficientVertex v)
    main (n + 1) 2 S h (Pi.single s 1) inferInstance ![1] a =
      main n 2 (Option S) h.option (Pi.single (some s) 1) inferInstance ![1]
        (Option.elim · .point a) -
      match a s with
      | .hyperplane => (n : ℚ) * main (n - 1) 2 S h 0 inferInstance 0
          (Function.update a s .hyperplane)
      | .point => main n 2 S h 0 inferInstance 0 (Function.update a s .hyperplane)
      | _ => 0 := by
  dsimp only
  rw [remainderVertex_onePsi_plane_step, remainderContraction_onePsi_plane_line]

/-- All successive one-psi corrections at a one-degree plane remainder sum
to a binomial coefficient. These are coefficients, not new invariant values. -/
theorem remainderVertex_onePsi_plane_line (v : Variable .plane) (n : ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (a : S → SurfaceBasisLabel .plane) :
    let main := remainderVertex .plane v (planeCoefficientVertex v)
    main n 2 S h (Pi.single s 1) inferInstance ![1] a =
      match a s with
      | .hyperplane => -(n.choose 2 : ℚ) * main (n - 2) 2 S h 0 inferInstance 0
          (Function.update a s .hyperplane)
      | .point => -(n : ℚ) * main (n - 1) 2 S h 0 inferInstance 0
          (Function.update a s .hyperplane)
      | _ => 0 := by
  dsimp only
  induction n generalizing S with
  | zero =>
    rw [remainderVertex_plane_zero, if_neg (by decide)]
    cases a s <;> norm_num
  | succ n ih =>
    rw [remainderVertex_onePsi_plane_succ,
      ih (Option S) h.option (some s) (Option.elim · .point a)]
    have hu : Function.update (Option.elim · SurfaceBasisLabel.point a) (some s) .hyperplane =
        (Option.elim · .point (Function.update a s .hyperplane)) := by
      funext t
      cases t with
      | none =>
        rw [Function.update_of_ne (show (none : Option S) ≠ some s from by intro he; cases he)]
        rfl
      | some t =>
        by_cases ht : t = s
        · subst t
          simp only [Function.update_self, Option.elim_some]
        · simp only [Function.update_of_ne (fun he ↦ ht (Option.some.inj he)),
            Option.elim_some, Function.update_of_ne ht]
    simp only [Option.elim_some, hu]
    cases hs : a s with
    | unit => exact sub_self 0
    | exceptional i => exact Fin.elim0 i
    | hyperplane =>
      cases n with
      | zero => norm_num
      | succ n =>
        cases n with
        | zero => norm_num
        | succ n =>
          simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
          rw [remainderVertex_plane_primary_option v n S h 0 (Function.update a s .hyperplane),
            Nat.choose_succ_succ (n + 1 + 1) 1, Nat.choose_one_right]
          simp only [Nat.cast_add, Nat.cast_one]
          ring
    | point =>
      cases n with
      | zero => norm_num
      | succ n =>
        simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
        rw [remainderVertex_plane_primary_option v n S h 0 (Function.update a s .hyperplane)]
        simp only [Nat.cast_add, Nat.cast_one]
        ring

end AxiomaticGW.SurfaceGenusTwo
