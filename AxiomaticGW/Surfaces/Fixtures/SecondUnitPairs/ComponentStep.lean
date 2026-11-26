/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.BoundedScalarAncestorFuel
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoSecondUnitCache

/-! # Replaying a lower-genus boundary against checked component values

A lookup can replace a rational or elliptic recursion only at sufficient
cotangent fuel. Each term still uses the original loop, separating graph,
effective coordinates, marking assignments and node pairing.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceLowGenusPointCache
open SurfacePointBenchmarkCache
variable {X : SurfaceTarget}

/-- The coordinate evaluator on the certified rational and elliptic point backends. -/
abbrev pointCoordinateComponent (X : SurfaceTarget) :=
  coordinateComponent X (genusZero X) (genusOne X)

/-- At sufficient rational fuel, consume the complete queried value. -/
def rationalAt (get : SurfaceAncestorKey X → ℚ) (fuel : ℕ) (q : SurfaceAncestorKey X) : ℚ :=
  if q.genus = 0 ∧ q.totalPsi ≤ fuel then get q else boundRational X fuel q

theorem rationalAt_eq {get : SurfaceAncestorKey X → ℚ}
    (hget : ∀ q, get q = pointCoordinateComponent X q)
    (fuel : ℕ) : rationalAt get fuel = boundRational X fuel := by
  funext q
  unfold rationalAt
  split_ifs with h
  · rw [hget, pointCoordinateComponent, coordinateComponent, if_pos h.1, coordinateRationalFuel_eq,
      boundRational_eq, rationalFuel_eq X _ (genusZero_eq X)]
    rw [rationalFuel_eq X _ (genusZero_eq X)]
    exact SurfaceGenusZero.ancestorValueFuel_stable _ _ _ h.1 le_rfl h.2
  · rfl

/-- At sufficient elliptic fuel, consume the complete queried value. -/
def ellipticAt (get : SurfaceAncestorKey X → ℚ) (fuel : ℕ) (q : SurfaceAncestorKey X) : ℚ :=
  if q.genus = 1 ∧ q.totalPsi ≤ fuel then get q else boundElliptic X fuel q

theorem ellipticAt_eq {get : SurfaceAncestorKey X → ℚ}
    (hget : ∀ q, get q = pointCoordinateComponent X q)
    (fuel : ℕ) : ellipticAt get fuel = boundElliptic X fuel := by
  funext q
  unfold ellipticAt
  split_ifs with h
  · rw [hget, pointCoordinateComponent, coordinateComponent, if_neg (show q.genus ≠ 0 by omega),
      coordinateEllipticFuel_eq, boundElliptic_eq,
      ellipticFuel_eq X _ _ (genusZero_eq X) (genusOne_eq X)]
    rw [ellipticFuel_eq X _ _ (genusZero_eq X) (genusOne_eq X)]
    exact SurfaceGenusOne.ancestorValueFuel_stable _ _ _ h.1 le_rfl h.2
  · rfl

/-- All rational branches use their sufficient fuel. Elliptic branches retain the stage fuel. -/
def stagedEllipticStep (get : SurfaceAncestorKey X → ℚ) (fuel : ℕ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hp : ¬ q.IsPrimary) : ℚ :=
  ((PsiBoundaryExpansion.genusOneTerms (SurfaceGenusOne.extraCount q)).map fun t ↦
    t.1 * t.2.scalarSurfaceEval X
      (fun g S _ h beta k a ↦
        let r := SurfaceAncestorKey.ofLabels g S h beta k a
        if r.genus = 0 then get r else ellipticAt get fuel r)
      q.beta (SurfaceGenusOne.lowerAncestorPowers q hg hp)
        (q.orderedLabels ∘ SurfaceGenusOne.ancestorFrame q hg hp)).sum

theorem stagedEllipticStep_eq {get : SurfaceAncestorKey X → ℚ}
    (hget : ∀ q, get q = pointCoordinateComponent X q) (fuel : ℕ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hp : ¬ q.IsPrimary) :
    stagedEllipticStep get fuel q hg hp = boundEllipticStep X (boundElliptic X fuel) q hg hp := by
  have vertex (r : SurfaceAncestorKey X) :
      (if r.genus = 0 then get r else ellipticAt get fuel r) =
      (if r.genus = 0 then boundRational X r.totalPsi r else boundElliptic X fuel r) := by
    by_cases h : r.genus = 0
    · rw [if_pos h, if_pos h, hget, pointCoordinateComponent, ← boundValue_eq, boundValue, if_pos h]
    · rw [if_neg h, if_neg h, ellipticAt_eq hget]
  simp only [stagedEllipticStep, boundEllipticStep, vertex]

/-- Replay one full cotangent equation with previously checked lower-power components. -/
def stagedValue (get : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X) : ℚ :=
  match q.totalPsi with
  | 0 => boundValue X q
  | n + 1 =>
    if hg : q.genus = 0 then
      if q.insertions.card ≤ q.totalPsi + 2 then 0 else
      if hp : q.IsPrimary then rationalPrimary X (genusZero X) q.beta q.primaryLabels
      else scalarRationalStep (rationalAt get n) q hg hp
    else if he : q.genus = 1 then
      if q.insertions.card < q.totalPsi then 0 else
      if hp : q.IsPrimary then ellipticPrimary X (genusOne X) q.beta q.primaryLabels
      else stagedEllipticStep get n q he hp
    else 0

theorem stagedValue_eq {get : SurfaceAncestorKey X → ℚ}
    (hget : ∀ q, get q = pointCoordinateComponent X q) (q : SurfaceAncestorKey X) :
    stagedValue get q = pointCoordinateComponent X q := by
  rw [pointCoordinateComponent, ← boundValue_eq]
  unfold stagedValue
  split
  · rfl
  · rename_i n he
    unfold boundValue
    rw [he]
    by_cases hz : q.genus = 0
    · rw [dif_pos hz, if_pos hz, boundRational, dif_pos hz, rationalAt_eq hget, he]
    · rw [dif_neg hz, if_neg hz, boundElliptic]
      by_cases ho : q.genus = 1
      · simp only [dif_pos ho, stagedEllipticStep_eq hget, he]
      · rw [dif_neg ho, dif_neg ho]

end AxiomaticGW.SurfaceLowGenusPointCache

namespace AxiomaticGW.SurfaceGenusTwoPositiveSquare
open SurfaceLowGenusPointCache
variable {X : SurfaceTarget}

/-- Retain the previous stage for all keys absent from this bucket. -/
def stageLookup (previous : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X) :
    List (Entry X) → ℚ
  | [] => previous q
  | e :: rest => if q = e.key then e.value else stageLookup previous q rest

theorem stageLookup_eq (previous : SurfaceAncestorKey X → ℚ)
    (hprevious : ∀ q, previous q = pointCoordinateComponent X q) (q : SurfaceAncestorKey X)
    (rows : List (Entry X)) : stageLookup previous q rows = pointCoordinateComponent X q := by
  induction rows with
  | nil => exact hprevious q
  | cons e rest ih =>
    by_cases h : q = e.key
    · rw [stageLookup, if_pos h, h]
      exact e.checked
    · rw [stageLookup, if_neg h, ih]

end AxiomaticGW.SurfaceGenusTwoPositiveSquare
