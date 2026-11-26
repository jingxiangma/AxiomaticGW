/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.CurveSum
public import AxiomaticGW.Surfaces.LowGenusPointCache

/-! # Exact effective-coordinate evaluation of rational and elliptic ancestor steps

For a scalar coefficient, each separating edge needs only the first effective
summand and one node basis class. A zero factor skips its complement. The
result is compared to the existing finite-fuel definition at every component.
-/

@[expose] public section
namespace AxiomaticGW.GluingExpression

/-- Evaluate the original gluing expression with coordinate sums and scalar zero checks. -/
def scalarSurfaceEval (X : SurfaceTarget) (vertex : SurfaceVertexValues X ℚ) :
    {g : ℕ} → {S : Type} → [Fintype S] → GluingExpression g S →
      X.Curve → (S → ℕ) → (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @fundamental g S _ h, beta, k, a => vertex g S h beta k a
  | _, _, _, @relabel _ _ _ _ _ e x, beta, k, a =>
      scalarSurfaceEval X vertex x beta (k ∘ e) (a ∘ e)
  | _, _, _, @separating _ _ _ _ _ _ x y, beta, k, a =>
    X.sumSubcurves beta fun c ↦ ∑ b : SurfaceBasisLabel X, b.inverseWeight *
      (let left := scalarSurfaceEval X vertex x c (PsiClasses.separatingLeftPowers k)
         (Option.elim · b (a ∘ Sum.inl))
       if left = 0 then 0 else left *
         scalarSurfaceEval X vertex y (beta - c) (PsiClasses.separatingRightPowers k)
           (Option.elim · b.dual (a ∘ Sum.inr)))
  | _, _, _, @nonseparating _ _ _ x, beta, k, a =>
    ∑ b : SurfaceBasisLabel X, b.inverseWeight *
      scalarSurfaceEval X vertex x beta (PsiClasses.nonseparatingPowers k)
        (Option.elim · b (fun t ↦ Option.elim t b.dual a))

theorem scalarSurfaceEval_eq (X : SurfaceTarget) (vertex : SurfaceVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    scalarSurfaceEval X vertex x beta k a = x.surfaceEval X vertex beta k a := by
  have skip (a b : ℚ) : (if a = 0 then 0 else a * b) = a * b := by
    split_ifs with h
    · rw [h, zero_mul]
    · rfl
  induction x generalizing beta with
  | fundamental => rfl
  | relabel e x ih => exact ih beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    simp only [scalarSurfaceEval, surfaceEval, skip, ihx, ihy, Algebra.algebraMap_self_apply,
      SurfaceTarget.sumSubcurves_eq, SurfaceTarget.splittings, WeightedCurveClass.splittings]
    rw [Finset.sum_image (fun _ _ _ _ h ↦ congrArg Prod.fst h)]
  | nonseparating x ih =>
    simp only [scalarSurfaceEval, surfaceEval, ih, Algebra.algebraMap_self_apply]

end AxiomaticGW.GluingExpression

namespace AxiomaticGW.SurfaceLowGenusPointCache

/-- The rational cotangent equation with scalar contraction at every boundary graph. -/
def scalarRationalStep {X : SurfaceTarget} (next : SurfaceAncestorKey X → ℚ)
    (q : SurfaceAncestorKey X) (hg : q.genus = 0) (hp : ¬q.IsPrimary) : ℚ :=
  ((PsiBoundaryExpansion.genusZeroTerms 0 (SurfaceGenusZero.extraCount q)).map fun t ↦
    t.1 * t.2.scalarSurfaceEval X
      (fun g S _ h beta k a ↦ next (SurfaceAncestorKey.ofLabels g S h beta k a))
      q.beta (SurfaceGenusZero.lowerAncestorPowers q hg hp)
        (q.orderedLabels ∘ SurfaceGenusZero.ancestorFrame q hg hp)).sum

/-- The elliptic loop and separating equations with the proved rational primary backend. -/
def scalarEllipticStep {X : SurfaceTarget} (v₀ : X.Curve → ℚ)
    (next : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hp : ¬q.IsPrimary) : ℚ :=
  ((PsiBoundaryExpansion.genusOneTerms (SurfaceGenusOne.extraCount q)).map fun t ↦
    t.1 * t.2.scalarSurfaceEval X
      (fun g S _ h beta k a ↦
        let r := SurfaceAncestorKey.ofLabels g S h beta k a
        if r.genus = 0 then rationalValue X v₀ r else next r)
      q.beta (SurfaceGenusOne.lowerAncestorPowers q hg hp)
        (q.orderedLabels ∘ SurfaceGenusOne.ancestorFrame q hg hp)).sum

/-- Use coordinate enumeration in the top boundary step, including every cotangent placement. -/
def scalarComponentValue (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (q : SurfaceAncestorKey X) : ℚ :=
  match q.totalPsi with
  | 0 => componentValue X v₀ v₁ q
  | fuel + 1 =>
    if hp : q.IsPrimary then componentValue X v₀ v₁ q else
    if h₀ : q.genus = 0 then scalarRationalStep (rationalFuel X v₀ fuel) q h₀ hp else
    if h₁ : q.genus = 1 then scalarEllipticStep v₀ (ellipticFuel X v₀ v₁ fuel) q h₁ hp else 0

theorem scalarComponentValue_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (q : SurfaceAncestorKey X) : scalarComponentValue X v₀ v₁ q = componentValue X v₀ v₁ q := by
  unfold scalarComponentValue
  split
  · rfl
  · rename_i fuel he
    by_cases hp : q.IsPrimary
    · rw [dif_pos hp]
    rw [dif_neg hp]
    by_cases h₀ : q.genus = 0
    · simp only [dif_pos h₀, componentValue, if_pos h₀, rationalValue, he, rationalFuel,
        dif_neg hp, scalarRationalStep, SurfaceGenusZero.ancestorStep,
        GluingExpression.scalarSurfaceEval_eq]
    · rw [dif_neg h₀, componentValue, if_neg h₀, ellipticValue, he, ellipticFuel]
      by_cases h₁ : q.genus = 1
      · simp only [dif_pos h₁, dif_neg hp, scalarEllipticStep, ellipticStep,
          GluingExpression.scalarSurfaceEval_eq]
      · simp only [dif_neg h₁]

end AxiomaticGW.SurfaceLowGenusPointCache
