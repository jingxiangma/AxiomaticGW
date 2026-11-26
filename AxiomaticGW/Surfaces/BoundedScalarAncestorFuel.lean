/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarAncestorFuel
public import AxiomaticGW.Surfaces.LowGenusAncestorDimension
public import AxiomaticGW.Surfaces.PointBenchmarkCache

/-! # Stable-curve dimension pruning at every rational and elliptic boundary

The tests use the cotangent dimension of the moduli space of stable curves.
They preserve every finite-fuel approximation on the canonical point
backend, including numerical queries at incompatible surface dimensions.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceLowGenusPointCache
open SurfacePointBenchmarkCache

/-- Skip rational descendants above the cotangent dimension at every recursive step. -/
def boundRational (X : SurfaceTarget) : ℕ → SurfaceAncestorKey X → ℚ
  | 0, q => rationalFuel X (genusZero X) 0 q
  | n + 1, q => if hg : q.genus = 0 then
      if q.insertions.card ≤ q.totalPsi + 2 then 0 else
      if hp : q.IsPrimary then rationalPrimary X (genusZero X) q.beta q.primaryLabels
      else scalarRationalStep (boundRational X n) q hg hp
    else 0

theorem boundRational_eq (X : SurfaceTarget) (n : ℕ) :
    boundRational X n = rationalFuel X (genusZero X) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext q
    rw [boundRational]
    split_ifs with hg hd hp
    · rw [rationalFuel_eq _ _ (genusZero_eq _)]
      exact (SurfaceGenusZero.ancestorValueFuel_zero_of_cotangent_bound _ q hg hd).symm
    · rw [rationalFuel, dif_pos hg, dif_pos hp]
    · rw [rationalFuel, dif_pos hg, dif_neg hp, ih]
      simp only [scalarRationalStep, SurfaceGenusZero.ancestorStep,
        GluingExpression.scalarSurfaceEval_eq]
    · rw [rationalFuel, dif_neg hg]

/-- The elliptic boundary uses the dimension test on each rational component. -/
def boundEllipticStep (X : SurfaceTarget) (next : SurfaceAncestorKey X → ℚ)
    (q : SurfaceAncestorKey X) (hg : q.genus = 1) (hp : ¬q.IsPrimary) : ℚ :=
  ((PsiBoundaryExpansion.genusOneTerms (SurfaceGenusOne.extraCount q)).map fun t ↦
    t.1 * t.2.scalarSurfaceEval X
      (fun g S _ h beta k a ↦
        let r := SurfaceAncestorKey.ofLabels g S h beta k a
        if r.genus = 0 then boundRational X r.totalPsi r else next r)
      q.beta (SurfaceGenusOne.lowerAncestorPowers q hg hp)
        (q.orderedLabels ∘ SurfaceGenusOne.ancestorFrame q hg hp)).sum

theorem boundEllipticStep_eq (X : SurfaceTarget) (next : SurfaceAncestorKey X → ℚ)
    (q : SurfaceAncestorKey X) (hg : q.genus = 1) (hp : ¬q.IsPrimary) :
    boundEllipticStep X next q hg hp = ellipticStep X (genusZero X) next q hg hp := by
  simp only [boundEllipticStep, ellipticStep, GluingExpression.scalarSurfaceEval_eq,
    boundRational_eq, rationalValue]

/-- Apply the stable-curve dimension tests to both genera in the elliptic recursion. -/
def boundElliptic (X : SurfaceTarget) : ℕ → SurfaceAncestorKey X → ℚ
  | 0, q => ellipticFuel X (genusZero X) (genusOne X) 0 q
  | n + 1, q => if hg : q.genus = 1 then
      if q.insertions.card < q.totalPsi then 0 else
      if hp : q.IsPrimary then ellipticPrimary X (genusOne X) q.beta q.primaryLabels
      else boundEllipticStep X (boundElliptic X n) q hg hp
    else 0

theorem boundElliptic_eq (X : SurfaceTarget) (n : ℕ) :
    boundElliptic X n = ellipticFuel X (genusZero X) (genusOne X) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext q
    rw [boundElliptic]
    split_ifs with hg hd hp
    · rw [ellipticFuel_eq _ _ _ (genusZero_eq _) (genusOne_eq _)]
      exact (SurfaceGenusOne.ancestorValueFuel_zero_of_cotangent_bound _ q hg hd).symm
    · rw [ellipticFuel, dif_pos hg, dif_pos hp]
    · rw [ellipticFuel, dif_pos hg, dif_neg hp, ih, boundEllipticStep_eq]
    · rw [ellipticFuel, dif_neg hg]

/-- Evaluate on the canonical lower-genus primary backend at the sufficient cotangent fuel. -/
def boundValue (X : SurfaceTarget) (q : SurfaceAncestorKey X) : ℚ :=
  if q.genus = 0 then boundRational X q.totalPsi q else boundElliptic X q.totalPsi q

theorem boundValue_eq (X : SurfaceTarget) (q : SurfaceAncestorKey X) :
    boundValue X q = coordinateComponent X (genusZero X) (genusOne X) q := by
  simp only [boundValue, coordinateComponent, boundRational_eq, boundElliptic_eq,
    coordinateRationalFuel_eq, coordinateEllipticFuel_eq]

end AxiomaticGW.SurfaceLowGenusPointCache
