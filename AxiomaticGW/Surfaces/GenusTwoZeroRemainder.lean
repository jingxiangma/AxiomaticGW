/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPointTails

/-!
# First-power plane coefficients with zero effective remainder

At zero remainder the new rational cotangent tail has degree zero. Its
classical triple is nonzero precisely for two units and the new point, and
it receives no further points. Iterating the signed correction therefore
gives a linear multiple of the primary main component.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

/-- The degree-zero cotangent tail is the classical unit-unit-point triple. -/
theorem primaryScalar_plane_zero_tail (n : ℕ) (b c : SurfaceBasisLabel .plane) :
    primaryScalar .plane (pointValue .plane) 0 n
      (Option.elim · b (fun t : Bool ↦ if t then .point else c)) =
      if n = 0 ∧ b = .unit ∧ c = .unit then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    cases b <;> cases c
    all_goals first | exact Fin.elim0 (show Fin 0 from ‹Fin 0›) | decide +kernel
  · have hc : n + Fintype.card (Option Bool) ≠ 3 := by
      simp only [Fintype.card_option, Fintype.card_bool]
      omega
    simp only [primaryScalar, ne_eq, not_true_eq_false, false_and, ite_false,
      ite_true, if_neg hc, ite_self, hn]

/-- No added point can lie on the classical tail. -/
theorem sum_binomial_primary_plane_zero_tail (f : ℕ → ℚ) (n : ℕ)
    (b c : SurfaceBasisLabel .plane) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * primaryScalar .plane (pointValue .plane) 0 ij.2
        (Option.elim · b (fun t : Bool ↦ if t then .point else c)))) =
      if b = .unit ∧ c = .unit then f n else 0 := by
  rw [SurfacePointPullback.sum_binomial_of_right_support f
    (fun j ↦ primaryScalar .plane (pointValue .plane) 0 j
      (Option.elim · b (fun t : Bool ↦ if t then .point else c))) n 0 (by
        intro j hj
        rw [primaryScalar_plane_zero_tail, if_neg (fun h ↦ hj h.1)])]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul,
    primaryScalar_plane_zero_tail, true_and, mul_ite, mul_one, mul_zero]

end AxiomaticGW.SurfaceGenusZero

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction GluingExpression

/-- At zero remainder the tail replaces an old unit by a point on the main
component. Every other old insertion gives zero. -/
theorem remainderContraction_onePsi_plane_zero (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (n : ℕ) (a : S → SurfaceBasisLabel .plane) :
    let z := CotangentTerm.tail h (Pi.single s 1) s
    remainderContraction .plane v main z.expression z.decoration z.labels
      0 n (Option.elim · .point a) =
      if a s = .unit then main n 2 S h 0 inferInstance 0 (Function.update a s .point)
      else 0 := by
  dsimp only
  rw [remainderContraction_onePsi_tail]
  rw [show SurfaceTarget.plane.splittings 0 = {(0, 0)} from
    (SurfaceTarget.plane.splittings_eq 0).trans
      SurfaceTarget.plane.effective.splittings_zero, Finset.sum_singleton]
  have hsum (b : SurfaceBasisLabel .plane) :=
    SurfaceGenusZero.sum_binomial_primary_plane_zero_tail
      (fun m ↦ main m 2 S h 0 inferInstance 0 (Function.update a s b)) n b.dual (a s)
  simp only [hsum]
  rw [SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    one_mul, Fin.sum_univ_zero, add_zero, reduceCtorEq, false_and,
    ite_false, true_and, zero_add]

/-- The zero-remainder first-power step retains its classical unit correction. -/
theorem remainderVertex_onePsi_plane_zero_succ (v : Variable .plane)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (n : ℕ) (a : S → SurfaceBasisLabel .plane) :
    let main := remainderVertex .plane v (planeCoefficientVertex v)
    main (n + 1) 2 S h (Pi.single s 1) inferInstance 0 a =
      main n 2 (Option S) h.option (Pi.single (some s) 1) inferInstance 0
        (Option.elim · .point a) -
      if a s = .unit then main n 2 S h 0 inferInstance 0 (Function.update a s .point)
      else 0 := by
  dsimp only
  rw [remainderVertex_onePsi_plane_step, remainderContraction_onePsi_plane_zero]

/-- Every point pullback at zero remainder contributes the same primary
unit correction. The original normalized terminal key is retained explicitly. -/
theorem remainderVertex_onePsi_plane_zero (v : Variable .plane) (n : ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (a : S → SurfaceBasisLabel .plane) :
    let main := remainderVertex .plane v (planeCoefficientVertex v)
    let q := SurfaceAncestorKey.ofLabels 2 S h (SurfaceGenusZero.variableCurve v)
      (Pi.single s 1) a
    main n 2 S h (Pi.single s 1) inferInstance 0 a =
      RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
        (residualTerms (q.addPoints n))) {v} -
      if a s = .unit then
        (n : ℚ) * main (n - 1) 2 S h 0 inferInstance 0 (Function.update a s .point)
      else 0 := by
  dsimp only
  induction n generalizing S with
  | zero =>
    rw [remainderVertex_plane_zero, if_pos rfl, planeCoefficientVertex_eq]
    simp only [coefficientVertex, ite_true, vertexTerms, SurfaceAncestorKey.addPoints_zero,
      Nat.cast_zero, zero_mul, ite_self, sub_zero]
  | succ n ih =>
    rw [remainderVertex_onePsi_plane_zero_succ,
      ih (Option S) h.option (some s) (Option.elim · .point a)]
    have hk : (Pi.single (some s) 1 : Option S → ℕ) =
        (Option.elim · 0 (Pi.single s 1)) := by
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
    have hu : Function.update (Option.elim · SurfaceBasisLabel.point a) (some s) .point =
        (Option.elim · .point (Function.update a s .point)) := by
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
    rw [hk, SurfaceAncestorKey.addPoints_ofLabels_option_powers 2 S h
      (SurfaceGenusZero.variableCurve v) (Pi.single s 1) a n]
    simp only [Option.elim_some, hu]
    by_cases hs : a s = .unit
    · rw [if_pos hs, if_pos hs, if_pos hs]
      cases n with
      | zero => simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, one_mul,
          sub_zero]
      | succ n =>
        simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
        rw [remainderVertex_plane_primary_option v n S h 0 (Function.update a s .point)]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
    · simp only [if_neg hs, sub_zero]

end AxiomaticGW.SurfaceGenusTwo
