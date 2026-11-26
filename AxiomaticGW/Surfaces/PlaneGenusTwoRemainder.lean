/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoRemainder
public import AxiomaticGW.Surfaces.PlaneGenusTwoCoefficients

/-!
# Plane coefficients from rational complements of a fixed degree

The complete signed contraction enumerates splittings of the difference
between the equation degree and the requested variable degree. With no added
points left, the genus-two component consumes no remainder: the proved plane
calibration cancellation fixes its class exactly. A one-degree shift therefore
uses only degree-zero and degree-one rational complements.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceTarget

/-- A line has precisely its two ordered effective decompositions. -/
theorem plane_splittings_one : plane.splittings ![1] =
    ({(0, ![1]), (![1], 0)} : Finset (plane.Curve × plane.Curve)) := by decide +kernel

/-- Each edge of a one-degree remainder has only these two class assignments. -/
theorem sum_plane_splittings_one {A : Type*} [AddCommMonoid A]
    (f : plane.Curve × plane.Curve → A) :
    (∑ p ∈ plane.splittings ![1], f p) = f (0, ![1]) + f (![1], 0) := by
  rw [plane_splittings_one, Finset.sum_pair (by decide)]

end AxiomaticGW.SurfaceTarget

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)

/-- All the effective remainder belongs to rational components, including the
signed cotangent tails: the final plane genus-two component consumes none. -/
theorem remainderVertex_plane_zero (v : Variable .plane)
    (S : Type) [Fintype S] (h : StableArity 2 S) (d : S → ℕ) (l : DecidableEq S)
    (delta : SurfaceTarget.plane.Curve) (a : S → SurfaceBasisLabel .plane) :
    remainderVertex .plane v (planeCoefficientVertex v) 0 2 S h d l delta a =
      if delta = 0 then planeCoefficientVertex v 2 S h (variableCurve v) d a else 0 := by
  rw [remainderVertex]
  dsimp only
  by_cases hz : delta = 0
  · rw [hz, add_zero, if_pos rfl]
  · have hne : variableCurve v ≠ variableCurve v + delta := by
      intro he
      apply hz
      apply add_left_cancel (a := variableCurve v)
      exact he.symm.trans (add_zero _).symm
    rw [if_neg hz, planeCoefficientVertex, if_pos rfl, if_neg hne]

/-- With no cotangent power, the main component consumes no remainder even
before its additional points have been placed. Its value is one normalized key. -/
theorem remainderVertex_plane_primary (v : Variable .plane) (n : ℕ)
    (S : Type) [Fintype S] (h : StableArity 2 S) (l : DecidableEq S)
    (delta : SurfaceTarget.plane.Curve) (a : S → SurfaceBasisLabel .plane) :
    remainderVertex .plane v (planeCoefficientVertex v) n 2 S h 0 l delta a =
      if delta = 0 then
        RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
          (residualTerms ((SurfaceAncestorKey.ofLabels 2 S h (variableCurve v) 0 a).addPoints n)))
            {v}
      else 0 := by
  rw [remainderVertex_eq _ _ _ (planeCoefficientVertex_eq v), vertex_primary_genusTwo_eq]
  by_cases hz : delta = 0
  · rw [hz, add_zero, if_pos rfl]
  · rw [if_neg hz]
    have hne : variableCurve v ≠ variableCurve v + delta := by
      intro he
      apply hz
      apply add_left_cancel (a := variableCurve v)
      exact he.symm.trans (add_zero _).symm
    let q := (SurfaceAncestorKey.ofLabels 2 S h (variableCurve v + delta) 0 a).addPoints n
    change RationalTerms.coefficient
      (RationalTerms.affineSubstitute normalizedTerms (residualTerms q)) {v} = 0
    simp only [residualTerms, if_neg (show ¬q.genus ≤ 1 from Nat.not_succ_le_self 1)]
    split_ifs with hd
    · simpa only [RationalTerms.coefficient_affineSubstitute_term,
        Multiset.map_singleton, Multiset.sum_singleton, one_mul,
        normalizedTerms_plane_eq_direct] using
        coefficient_directNormalizedTerms_eq_zero q le_rfl v hne
    · exact RationalTerms.coefficient_affineSubstitute_zero _ _

/-- A specified new primary point and one more counted point give the same
main-component coefficient, at every effective remainder. -/
theorem remainderVertex_plane_primary_option (v : Variable .plane) (n : ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S)
    (delta : SurfaceTarget.plane.Curve) (a : S → SurfaceBasisLabel .plane) :
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Option S) h.option
      0 inferInstance delta (Option.elim · .point a) =
      remainderVertex .plane v (planeCoefficientVertex v) (n + 1) 2 S h
        0 inferInstance delta a := by
  rw [remainderVertex_plane_primary, remainderVertex_plane_primary,
    SurfaceAncestorKey.addPoints_ofLabels_option 2 S h (variableCurve v) a n]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)

/-- The full BP point coefficient, splitting only the effective remainder. -/
def planeRemainderPointCoefficient (n : ℕ) (delta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) : ℚ :=
  ∑ i : Fin 4, rawPaperCoefficient (Fin.castAdd 16 i) * ∑ e,
    SurfaceGenusTwo.remainderPointCoefficient .plane v (SurfaceGenusTwo.planeCoefficientVertex v)
      (orbitCotangentTerm (Fin.castAdd 16 i) e) delta n a

/-- The degree shift changes the summation variables, not the BP equation. -/
theorem planeRemainderPointCoefficient_eq (n : ℕ) (delta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) :
    planeRemainderPointCoefficient n delta a v =
      pointCoefficient .plane n (variableCurve v + delta) a v := by
  simp only [planeRemainderPointCoefficient,
    SurfaceGenusTwo.remainderPointCoefficient_eq _ _ _
      (SurfaceGenusTwo.planeCoefficientVertex_eq v), pointCoefficient]

/-- Accept an absolute source degree, with an explicit order check before
subtraction. A request above the source degree has zero coefficient. -/
def planePointCoefficientByRemainder (n source : ℕ)
    (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) : ℚ :=
  if variableCurve v 0 ≤ source then
    planeRemainderPointCoefficient n ![source - variableCurve v 0] a v
  else 0

/-- The guarded source-degree interface agrees with the entire original consumer. -/
theorem planePointCoefficientByRemainder_eq (n source : ℕ)
    (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) :
    planePointCoefficientByRemainder n source a v =
      pointCoefficient .plane n ![source] a v := by
  unfold planePointCoefficientByRemainder
  split_ifs with h
  · rw [planeRemainderPointCoefficient_eq]
    have he : variableCurve v + ![source - variableCurve v 0] = ![source] := by
      funext i
      fin_cases i
      change variableCurve v 0 + (source - variableCurve v 0) = source
      omega
    rw [he]
  · have hnot : ¬variableCurve v ≤ (![source] : SurfaceTarget.plane.Curve) :=
      fun hl ↦ h (hl 0)
    simp only [pointCoefficient,
      SurfaceGenusTwo.pointCoefficient_eq_zero_of_not_le _ _ _ _ _ hnot,
      Finset.sum_const_zero, mul_zero]

end AxiomaticGW.BelorousskiPandharipande
