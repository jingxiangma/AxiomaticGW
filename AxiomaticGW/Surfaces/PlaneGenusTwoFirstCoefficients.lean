/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoScalarParts

/-!
# Direct nonprimary coefficients of low-psi plane components

A primary component cannot contribute to a variable containing a descendant.
A single cotangent power creates only primary rational-tail corrections, so
those coefficients have no tail contribution at any effective remainder.
The resulting terminal evaluation retains the full query, dimension check
and normalization. Every unsupported case uses the original evaluator.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction GluingExpression

/-- A normalized primary component has no coefficient at a nonprimary requested variable. -/
theorem coefficient_residualTerms_plane_primary_eq_zero_of_not_points (v : Variable .plane)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points .plane 2 beta n) ≠ v)
    (q : SurfaceAncestorKey .plane) (hg : q.genus = 2) (hp : q.IsPrimary) :
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (residualTerms q)) {v} = 0 := by
  rw [coefficient_residualTerms_plane_primary v q hg hp]
  split_ifs with hd
  · rw [SurfaceFirstDescendant.coefficient_rename_primaryTerms]
    simp only [if_neg (hv _ _), ite_self, mul_zero]
  · rfl

/-- Every primary main component vanishes in a nonprimary coefficient, at every remainder. -/
theorem remainderVertex_plane_primary_eq_zero_of_not_points (v : Variable .plane)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points .plane 2 beta n) ≠ v)
    (n : ℕ) (S : Type) [Fintype S] (h : StableArity 2 S) (l : DecidableEq S)
    (delta : SurfaceTarget.plane.Curve) (a : S → SurfaceBasisLabel .plane) :
    remainderVertex .plane v (planeCoefficientVertex v) n 2 S h 0 l delta a = 0 := by
  rw [remainderVertex_plane_primary]
  split_ifs with hd
  · apply coefficient_residualTerms_plane_primary_eq_zero_of_not_points v hv _ rfl
    intro t ht
    rcases Multiset.mem_add.mp ht with ht | ht
    · exact congrArg SurfaceInsertion.psi (Multiset.mem_replicate.mp ht).2
    · obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
      rfl
  · rfl

/-- A single psi can create only primary rational-tail corrections. They vanish
in a nonprimary coefficient, leaving the terminal key only at zero remainder. -/
theorem remainderVertex_plane_onePsi_of_not_points (v : Variable .plane)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points .plane 2 beta n) ≠ v)
    (n : ℕ) (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (delta : SurfaceTarget.plane.Curve) (a : S → SurfaceBasisLabel .plane) :
    remainderVertex .plane v (planeCoefficientVertex v) n 2 S h (Pi.single s 1)
      inferInstance delta a =
      if delta = 0 then
        RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
          (residualTerms ((SurfaceAncestorKey.ofLabels 2 S h (SurfaceGenusZero.variableCurve v)
            (Pi.single s 1) a).addPoints n))) {v}
      else 0 := by
  induction n generalizing S with
  | zero =>
    rw [remainderVertex_plane_zero]
    simp only [SurfaceAncestorKey.addPoints_zero, planeCoefficientVertex_eq,
      coefficientVertex, ite_true, vertexTerms]
  | succ n ih =>
    rw [remainderVertex_onePsi_plane_step, remainderContraction_onePsi_tail]
    simp only [remainderVertex_plane_primary_eq_zero_of_not_points v hv, zero_mul, mul_zero,
      Finset.sum_const_zero, sub_zero]
    rw [ih (Option S) h.option (some s) (Option.elim · .point a)]
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
    rw [hk, SurfaceAncestorKey.addPoints_ofLabels_option_powers 2 S h
      (SurfaceGenusZero.variableCurve v) (Pi.single s 1) a n]

/-- With total psi degree at most one, nonprimary coefficients need no point recursion. -/
theorem remainderVertex_plane_lowPsi_of_not_points (v : Variable .plane)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points .plane 2 beta n) ≠ v)
    (n : ℕ) (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S)
    (d : S → ℕ) (hd : ∑ s, d s ≤ 1)
    (delta : SurfaceTarget.plane.Curve) (a : S → SurfaceBasisLabel .plane) :
    remainderVertex .plane v (planeCoefficientVertex v) n 2 S h d
      inferInstance delta a =
      if delta = 0 then
        RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
          (residualTerms ((SurfaceAncestorKey.ofLabels 2 S h (SurfaceGenusZero.variableCurve v)
            d a).addPoints n))) {v}
      else 0 := by
  by_cases hz : d = 0
  · rw [hz, remainderVertex_plane_primary]
  · obtain ⟨s, hs⟩ := Function.ne_iff.mp hz
    have hsingle : d = Pi.single s 1 := by
      have hsmall := Finset.sum_le_one_iff.mp hd
      funext t
      by_cases ht : t = s
      · subst t
        rw [Pi.single_eq_same]
        exact (hsmall s s (Finset.mem_univ _) (Finset.mem_univ _) hs hs).2
      · rw [Pi.single_eq_of_ne ht]
        by_contra hne
        exact ht (hsmall t s (Finset.mem_univ _) (Finset.mem_univ _) hne hs).1
    rw [hsingle]
    exact remainderVertex_plane_onePsi_of_not_points v hv n S h s delta a

/-- Detect a requested numerical query containing a positive descendant power. -/
def requestsPositivePsi (v : Variable .plane) : Bool :=
  match v with
  | .inl _ => false
  | .inr q => q.insertions.any (fun t ↦ decide (t.psi ≠ 0))

/-- Every primary point query fails the positive-power guard. -/
theorem requestsPositivePsi_points (beta : SurfaceTarget.plane.Curve) (n : ℕ) :
    requestsPositivePsi (Sum.inr (SurfaceQuery.points .plane 2 beta n)) = false := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- A positive power distinguishes the full requested query from every primary point query. -/
theorem not_points_of_requestsPositivePsi (v : Variable .plane)
    (hv : requestsPositivePsi v = true) (beta : SurfaceTarget.plane.Curve) (n : ℕ) :
    Sum.inr (SurfaceQuery.points .plane 2 beta n) ≠ v := by
  intro he
  rw [← he, requestsPositivePsi_points] at hv
  cases hv

/-- Use the proved terminal formula when applicable and retain the original
evaluator for every other genus, decoration and requested variable. -/
def planeLowPsiCoefficientVertex (v : Variable .plane) (n : ℕ) :
    SurfaceCotangentVertexValues .plane ℚ :=
  fun g S _ h d l delta a ↦
    if g = 2 ∧ (∑ s, d s) ≤ 1 ∧ requestsPositivePsi v = true then
      if d = 0 then 0
      else if delta = 0 then
        RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
          (residualTerms ((SurfaceAncestorKey.ofLabels g S h (SurfaceGenusZero.variableCurve v)
            d a).addPoints n))) {v}
      else 0
    else planeCachedRemainderVertex v n g S h d l delta a

/-- The optimized vertex agrees with the complete original signed point recursion. -/
theorem planeLowPsiCoefficientVertex_eq (v : Variable .plane) (n : ℕ) :
    planeLowPsiCoefficientVertex v n = planeCachedRemainderVertex v n := by
  funext g S _ h d l delta a
  unfold planeLowPsiCoefficientVertex
  split_ifs with hc hz hd
  · obtain ⟨rfl, _, hv⟩ := hc
    subst d
    rw [planeCachedRemainderVertex_eq,
      remainderVertex_plane_primary_eq_zero_of_not_points v
        (not_points_of_requestsPositivePsi v hv)]
  · obtain ⟨rfl, hpsi, hv⟩ := hc
    rw [planeCachedRemainderVertex_eq, remainderVertex_plane_lowPsi_of_not_points v
      (not_points_of_requestsPositivePsi v hv) n S h d hpsi delta a, if_pos hd]
  · obtain ⟨rfl, hpsi, hv⟩ := hc
    rw [planeCachedRemainderVertex_eq, remainderVertex_plane_lowPsi_of_not_points v
      (not_points_of_requestsPositivePsi v hv) n S h d hpsi delta a, if_neg hd]
  · rfl

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo
open SurfaceGenusZero (variableCurve)

/-- The original guarded BP contribution with a proved main-component shortcut. -/
def planePointCoefficientPartFast (n source : ℕ) (a : Fin 3 → SurfaceBasisLabel .plane)
    (v : Variable .plane) (k : Fin 4) (e : Fin 6) : ℚ :=
  if variableCurve v 0 ≤ source then
    let z := orbitCotangentTerm (Fin.castAdd 16 k) e
    rawPaperCoefficient (Fin.castAdd 16 k) *
      (if z.expression.maxComponentGenus = 2 then
        planeCachedRemainderContraction v (planeLowPsiCoefficientVertex v) z.expression
          z.decoration z.labels ![source - variableCurve v 0] n a
       else 0)
  else 0

/-- Every graph, state assignment, signed weight and effective remainder is unchanged. -/
theorem planePointCoefficientPartFast_eq (n source : ℕ)
    (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) (k : Fin 4) (e : Fin 6) :
    planePointCoefficientPartFast n source a v k e =
      planePointCoefficientPart n source a v k e := by
  have hv : planeLowPsiCoefficientVertex v = planeCachedRemainderVertex v :=
    funext (planeLowPsiCoefficientVertex_eq v)
  simp only [planePointCoefficientPartFast, planePointCoefficientPart, hv]

/-- Apply the same vertex identity to every original HHP/HPP/PPP component. -/
def planeEarlierCoefficientPartFast (d : ℕ) (i : Fin 3) (b : ℕ) (j : Fin 3)
    (k : Fin 4) (e : Fin 6) : ℚ :=
  let v : Variable .plane := Sum.inr (planeCanonicalQueries b j)
  match i.val with
  | 0 => planePointCoefficientPartFast (3 * d + 1) (d + 1)
      ![.hyperplane, .hyperplane, .point] v k e
  | 1 => planePointCoefficientPartFast (3 * d) (d + 1)
      ![.hyperplane, .point, .point] v k e
  | _ => planePointCoefficientPartFast (3 * d - 1) (d + 1)
      ![.point, .point, .point] v k e

/-- The exact coefficient claim is preserved; no sampled value or formula is assumed. -/
theorem planeEarlierCoefficientPartFast_eq (d : ℕ) (i : Fin 3) (b : ℕ) (j : Fin 3)
    (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPartFast d i b j k e =
      planeEarlierCoefficientPart d i b j k e := by
  fin_cases i <;> exact planePointCoefficientPartFast_eq _ _ _ _ _ _

end AxiomaticGW.BelorousskiPandharipande
