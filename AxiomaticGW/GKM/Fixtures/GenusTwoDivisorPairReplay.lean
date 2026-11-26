/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoDivisorPairClaims
public import AxiomaticGW.GKM.Fixtures.GenusTwoOneMarkingReplay
public import AxiomaticGW.GKM.Fixtures.BlowupTwoLineOneMarkingReplay
public import AxiomaticGW.Surfaces.GenusTwoBlowupUnitPairs
public import AxiomaticGW.Surfaces.GenusTwoFewMarkings

/-! # Genus-two two-marked primary divisor comparisons

The plane and the two blowups use the same two-term divisor formula. At the strict
line the remaining unknown singleton is the canonical H value. Its signed multiplier
is exhibited even when it is nonzero.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoDivisorPairs
open SurfaceGenusTwo
variable {X : SurfaceTarget}

private def bindsSingletons (q main cup : SurfaceQuery X) : Bool :=
  match divisorPairReduction? q with
  | some (d, s) => decide (⟨2, q.beta, [s]⟩ = main ∧ cup.beta = q.beta ∧
      (cupCoefficient d s ≠ 0 → ⟨2, q.beta, [cupInsertion d s]⟩ = cup))
  | none => false

/-- The two signed multipliers, read from the full divisor-pair query. -/
def weights (q : SurfaceQuery X) : ℚ × ℚ :=
  match divisorPairReduction? q with
  | some (d, s) => (d.primaryFactor q.beta, cupCoefficient d s)
  | none => (0, 0)

private theorem compare (one : SurfaceQuery X → Option ℚ) (q main cup : SurfaceQuery X)
    (a b : ℚ) (hm : bindsSingletons q main cup = true)
    (ha : one main = some a) (hb : one cup = some b) :
    divisorPairValueWith? one q = some ((weights q).1 * a + (weights q).2 * b) := by
  cases hr : divisorPairReduction? q with
  | none => simp only [bindsSingletons, hr, Bool.false_eq_true] at hm
  | some ds =>
    obtain ⟨d, s⟩ := ds
    simp only [bindsSingletons, hr, decide_eq_true_eq] at hm
    rw [weights, hr]
    apply divisorPairValueWith?_of_singletons one q d s a b hr
    · intro _; rw [hm.1]; exact ha
    · intro h; rw [hm.2.2 h]; exact hb

-- Singleton order within each full class is unit, its divisor basis, then point.
private def cupIndex {n m : ℕ} [NeZero n] (j : Fin n) (d : Fin m) : Fin n :=
  let size := m + 2
  Fin.ofNat n (j.val / size * size + if j.val % size = 0 then d.val + 1 else size - 1)

namespace Plane

private abbrev single := GenusTwoOneMarking.Plane.requests
private abbrev value := GenusTwoOneMarking.Plane.values

/-- Each ordinary localization claim agrees with the full-class divisor formula. -/
theorem accepted (j : Fin 3) (d : Fin 1) (o : Fin 2) :
    FewMarkingQuery (requests j d o) ∧
    divisorPairValueWith? BelorousskiPandharipande.planeQueryValue? (requests j d o) =
      some (values j d o) := by
  refine ⟨?_, ?_⟩
  · revert j d o; unfold FewMarkingQuery; decide +kernel
  · have hm : bindsSingletons (requests j d o) (single j) (single (cupIndex j d)) = true := by
      revert j d o; decide +kernel
    have hv : (weights (requests j d o)).1 * value j +
        (weights (requests j d o)).2 * value (cupIndex j d) = values j d o := by
      revert j d o; decide +kernel
    exact (compare BelorousskiPandharipande.planeQueryValue? _ _ _ _ _ hm
      (GenusTwoOneMarking.Plane.accepted j)
      (GenusTwoOneMarking.Plane.accepted (cupIndex j d))).trans (congrArg some hv)

/-- Existing independent plane reconstruction also computes the unmodified ordered requests. -/
theorem original (j : Fin 3) (d : Fin 1) (o : Fin 2) :
    BelorousskiPandharipande.planeQueryValue? (requests j d o) = some (values j d o) := by
  apply planeFewMarkingBenchmark?_sound
  revert j d o; decide +kernel

/-- For H·H the lowered point singleton is nonzero. Dropping it changes both marking orders. -/
theorem square_parts (o : Fin 2) :
    (weights (requests 1 0 o)).1 * GenusTwoOneMarking.Plane.values 1 = -1/960 ∧
    (weights (requests 1 0 o)).2 * GenusTwoOneMarking.Plane.values 2 = -1/240 ∧
    values 1 0 o = -1/192 := by
  fin_cases o <;> decide +kernel

end Plane

namespace OneBlowup

private abbrev single := GenusTwoOneMarking.OneBlowup.requests
private abbrev value := GenusTwoOneMarking.OneBlowup.values

/-- Each ordinary localization claim agrees with the full-class divisor formula. -/
theorem accepted (j : Fin 4) (d : Fin 2) (o : Fin 2) :
    FewMarkingQuery (requests j d o) ∧
    divisorPairValue? 0 (requests j d o) = some (values j d o) := by
  refine ⟨?_, ?_⟩
  · revert j d o; unfold FewMarkingQuery; decide +kernel
  · have hm : bindsSingletons (requests j d o) (single j) (single (cupIndex j d)) = true := by
      revert j d o; decide +kernel
    have hv : (weights (requests j d o)).1 * value j +
        (weights (requests j d o)).2 * value (cupIndex j d) = values j d o := by
      revert j d o; decide +kernel
    exact (compare (SurfaceGenusTwoBlowupDescendants.queryValue? 0) _ _ _ _ _ hm
      (GenusTwoOneMarking.OneBlowup.accepted j)
      (GenusTwoOneMarking.OneBlowup.accepted (cupIndex j d))).trans (congrArg some hv)

end OneBlowup

namespace TwoBlowups

private abbrev single := GenusTwoOneMarking.TwoBlowups.requests
private abbrev value := GenusTwoOneMarking.TwoBlowups.values

/-- Each ordinary localization claim agrees with the full-class divisor formula. -/
theorem accepted (j : Fin 10) (d : Fin 3) (o : Fin 2) :
    FewMarkingQuery (requests j d o) ∧
    divisorPairValue? 0 (requests j d o) = some (values j d o) := by
  refine ⟨?_, ?_⟩
  · revert j d o; unfold FewMarkingQuery; decide +kernel
  · have hm : bindsSingletons (requests j d o) (single j) (single (cupIndex j d)) = true := by
      revert j d o; decide +kernel
    have hv : (weights (requests j d o)).1 * value j +
        (weights (requests j d o)).2 * value (cupIndex j d) = values j d o := by
      revert j d o; decide +kernel
    exact (compare (SurfaceGenusTwoBlowupDescendants.queryValue? 0) _ _ _ _ _ hm
      (GenusTwoOneMarking.TwoBlowups.accepted j)
      (GenusTwoOneMarking.TwoBlowups.accepted (cupIndex j d))).trans (congrArg some hv)

end TwoBlowups

namespace StrictLine
open BlowupTwoLineBP BlowupTwoLineOneMarking

private abbrev single := BlowupTwoLineOneMarkingReplay.requests
private abbrev value := BlowupTwoLineOneMarkingReplay.values
private abbrev H := SurfaceGenusTwoBlowupRecursion.values 0 (line, .hyperplane)
private def pointFlag (j : Fin 5) : ℚ := if j = 4 then 1 else 0

private theorem single_exact (j : Fin 5) :
    SurfaceGenusTwoBlowupDescendants.queryValue? 0 (single j) =
      some (value j + pointFlag j * H) := by
  by_cases h : j.val < 4
  · let k : Fin 4 := ⟨j.val, h⟩
    have hj : k.castSucc = j := Fin.ext rfl
    have he := BlowupTwoLineOneMarkingReplay.high_accepted k
    rw [hj] at he
    have hn : j ≠ 4 := by intro e; have he := congrArg Fin.val e; omega
    simpa only [pointFlag, if_neg hn, zero_mul, add_zero] using he
  · have hj : j = 4 := Fin.ext (by omega)
    subst j
    have he : single 4 = pointRequest := by decide +kernel
    rw [he, point_descendant, pointFlag, if_pos rfl, one_mul]
    change some H = some (0 + H)
    rw [zero_add]

/-- The primary point correction enters with the divisor self-intersection, while a surviving
point has coefficient one from pairing the divisor with L. -/
def discrepancy (j : Fin 5) (d : Fin 3) : ℚ :=
  if j = 4 then 1 else if j.val = d.val + 1 then (if d = 0 then 1 else -1) else 0

/-- Exact comparison of all 30 native strict-line rows, including each pending H term. -/
theorem comparison (j : Fin 5) (d : Fin 3) (o : Fin 2) :
    FewMarkingQuery (requests j d o) ∧ divisorPairValue? 0 (requests j d o) =
      some (values j d o + discrepancy j d * SurfaceGenusTwoBlowupRecursion.values 0
        (line, .hyperplane)) := by
  refine ⟨?_, ?_⟩
  · revert j d o; unfold FewMarkingQuery; decide +kernel
  · let c := cupIndex j d
    have hm : bindsSingletons (requests j d o) (single j) (single c) = true := by
      dsimp only [c]; revert j d o; decide +kernel
    have hv : (weights (requests j d o)).1 * value j + (weights (requests j d o)).2 * value c =
        values j d o := by dsimp only [c]; revert j d o; decide +kernel
    have hh : (weights (requests j d o)).1 * pointFlag j +
        (weights (requests j d o)).2 * pointFlag c = discrepancy j d := by
      dsimp only [c]; revert j d o; decide +kernel
    refine (compare (SurfaceGenusTwoBlowupDescendants.queryValue? 0) _ _ _ _ _ hm
      (single_exact j) (single_exact c)).trans (congrArg some ?_)
    rw [← hv, ← hh]
    ring

/-- The eighteen rows with zero discrepancy already agree at the original strict-line class. -/
theorem accepted (j : Fin 5) (d : Fin 3) (o : Fin 2) (h : discrepancy j d = 0) :
    divisorPairValue? 0 (requests j d o) = some (values j d o) := by
  simpa only [h, zero_mul, add_zero] using (comparison j d o).2

end StrictLine
end AxiomaticGW.GKM.GenusTwoDivisorPairs
