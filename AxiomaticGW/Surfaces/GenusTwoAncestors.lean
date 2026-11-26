/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoAncestorMarkings
public import AxiomaticGW.Surfaces.GenusTwoPsiReduction

/-!
# Terminating genus-two ancestor reduction to total psi degree at most one

Square or product selection removes two powers in the query's actual marking
frame. Every residual genus-two term has strictly smaller total psi degree.
The lower genera are already evaluated by their existing finite-seed
algorithms. This module proves termination and determination by the terminal
family; identifying that family and the recursive step with geometry is a
separate obligation for each target, not an additional numerical oracle.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
variable {X : SurfaceTarget}

/-- Complete signed reduction at the actual selected square or product. -/
def ancestorReductionTerms (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi) :
    RationalTerms (SurfaceAncestorKey X) :=
  if hs : (squareMarks q).Nonempty then
    boundaryReductionTerms X (GenusTwoPsiSquare.boundaryRemainder
      (q.orderedInsertions.length - 1)) q.beta (squareLowerPowers q hs)
        (q.orderedLabels ∘ squareFrame q hs)
  else
    boundaryReductionTerms X (GenusTwoPsiProduct.boundaryRemainder
      (q.orderedInsertions.length - 2)) q.beta (productLowerPowers q hk hs)
        (q.orderedLabels ∘ productFrame q hk hs)

/-- Every uncollected dependency is a dimension-compatible genus-two query
with strictly smaller total psi degree and an effective full-class remainder. -/
theorem ancestorReductionTerms_dependency (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    {t : ℚ × Multiset (SurfaceAncestorKey X)} (ht : t ∈ ancestorReductionTerms q hk)
    (r : SurfaceAncestorKey X) (hr : r ∈ t.2) :
    r.genus = 2 ∧ r.DimensionCompatible ∧ r.totalPsi < q.totalPsi ∧
      (r.beta = q.beta ∨ X.effective.energy r.beta < X.effective.energy q.beta) := by
  unfold ancestorReductionTerms at ht
  split_ifs at ht with hs
  · have hb := boundaryReductionTerms_dependency X _
      (GenusTwoPsiSquare.boundaryRemainder_bounds _) q.beta _ _ ht r hr
    have hsum := sum_squareLowerPowers q hs
    exact ⟨hb.1, hb.2.1, by omega, hb.2.2.2⟩
  · have hb := boundaryReductionTerms_dependency X _
      (GenusTwoPsiProduct.boundaryRemainder_bounds _) q.beta _ _ ht r hr
    have hsum := sum_productLowerPowers q hk hs
    exact ⟨hb.1, hb.2.1, by omega, hb.2.2.2⟩

/-- Evaluate the signed reduction using a valuation of its residual genus-two queries. -/
def ancestorStep (next : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hk : 1 < q.totalPsi) : ℚ := RationalTerms.eval next (ancestorReductionTerms q hk)

theorem ancestorStep_congr (v w : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hk : 1 < q.totalPsi)
    (hv : ∀ r : SurfaceAncestorKey X, r.genus = 2 → r.totalPsi < q.totalPsi → v r = w r) :
    ancestorStep v q hk = ancestorStep w q hk := by
  apply RationalTerms.eval_congr
  intro t ht r hr
  have hb := ancestorReductionTerms_dependency q hk ht r hr
  exact hv r hb.1 hb.2.2.1

/-- Structural recursion, parameterized only by the remaining low-psi
family. The parameter is consulted exclusively at total psi degree at most one. -/
def ancestorValueFuel (base : SurfaceAncestorKey X → ℚ) : ℕ → SurfaceAncestorKey X → ℚ
  | 0, q => if q.genus = 2 ∧ q.totalPsi ≤ 1 then base q else 0
  | fuel + 1, q => if hg : q.genus = 2 then
      if hk : q.totalPsi ≤ 1 then base q
      else ancestorStep (ancestorValueFuel base fuel) q (by omega)
    else 0

/-- Reconstruct from the low-psi terminal family using total psi degree as sufficient fuel.
Queries at other genera return zero. -/
def ancestorValue (base : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X) : ℚ :=
  ancestorValueFuel base q.totalPsi q

/-- A bounded terminal table suffices throughout its energy range, because
every residual full class has at most the original energy. -/
theorem ancestorValue_congr (v w : SurfaceAncestorKey X → ℚ) (bound : ℕ)
    (hv : ∀ r : SurfaceAncestorKey X, r.genus = 2 → r.totalPsi ≤ 1 →
      X.effective.energy r.beta ≤ bound → v r = w r)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2)
    (hb : X.effective.energy q.beta ≤ bound) : ancestorValue v q = ancestorValue w q := by
  have hf : ∀ (fuel : ℕ) (r : SurfaceAncestorKey X), r.genus = 2 →
      X.effective.energy r.beta ≤ bound → ancestorValueFuel v fuel r =
        ancestorValueFuel w fuel r := by
    intro fuel
    induction fuel with
    | zero =>
        intro r hgen hbound
        by_cases hk : r.totalPsi ≤ 1
        · rw [ancestorValueFuel, if_pos ⟨hgen, hk⟩,
            ancestorValueFuel, if_pos ⟨hgen, hk⟩]
          exact hv r hgen hk hbound
        · rw [ancestorValueFuel, if_neg (fun h ↦ hk h.2),
            ancestorValueFuel, if_neg (fun h ↦ hk h.2)]
    | succ fuel ih =>
        intro r hgen hbound
        rw [ancestorValueFuel, dif_pos hgen, ancestorValueFuel, dif_pos hgen]
        by_cases hk : r.totalPsi ≤ 1
        · rw [dif_pos hk, dif_pos hk]
          exact hv r hgen hk hbound
        · rw [dif_neg hk, dif_neg hk]
          apply RationalTerms.eval_congr
          intro t ht s hs
          have hd := ancestorReductionTerms_dependency r (by omega) ht s hs
          apply ih s hd.1
          rcases hd.2.2.2 with heq | hlt
          · rw [heq]
            exact hbound
          · omega
  exact hf q.totalPsi q hg hb

/-- The explicit query measure is a sufficient fuel bound. -/
theorem ancestorValueFuel_stable (base : SurfaceAncestorKey X → ℚ)
    (fuel more : ℕ) (q : SurfaceAncestorKey X) (hg : q.genus = 2)
    (hf : q.totalPsi ≤ fuel) (hm : q.totalPsi ≤ more) :
    ancestorValueFuel base fuel q = ancestorValueFuel base more q := by
  induction fuel generalizing more q with
  | zero =>
      have hk : q.totalPsi ≤ 1 := by omega
      cases more with
      | zero => rfl
      | succ more => rw [ancestorValueFuel, if_pos ⟨hg, hk⟩,
          ancestorValueFuel, dif_pos hg, dif_pos hk]
  | succ fuel ih =>
      by_cases hk : q.totalPsi ≤ 1
      · cases more with
        | zero =>
            symm
            rw [ancestorValueFuel, if_pos ⟨hg, hk⟩,
              ancestorValueFuel, dif_pos hg, dif_pos hk]
        | succ more => rw [ancestorValueFuel, dif_pos hg, dif_pos hk,
            ancestorValueFuel, dif_pos hg, dif_pos hk]
      · cases more with
        | zero => omega
        | succ more =>
            rw [ancestorValueFuel, dif_pos hg, dif_neg hk,
              ancestorValueFuel, dif_pos hg, dif_neg hk]
            apply ancestorStep_congr
            intro r hgen hpsi
            exact ih more r hgen (by omega) (by omega)

/-- The triangular equations determine a unique family once the low-psi
terminal values are fixed. The source-generator theorems derive the step
equations; this uniqueness theorem does not assert their geometric validity. -/
theorem ancestorValue_unique (base v : SurfaceAncestorKey X → ℚ)
    (hlow : ∀ q : SurfaceAncestorKey X, q.genus = 2 → q.totalPsi ≤ 1 → v q = base q)
    (hstep : ∀ (q : SurfaceAncestorKey X), q.genus = 2 →
      ∀ hk : 1 < q.totalPsi, v q = ancestorStep v q hk)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) : v q = ancestorValue base q := by
  have hf : ∀ (fuel : ℕ) (q : SurfaceAncestorKey X), q.genus = 2 → q.totalPsi ≤ fuel →
      v q = ancestorValueFuel base fuel q := by
    intro fuel
    induction fuel with
    | zero =>
        intro q hg hp
        have hk : q.totalPsi ≤ 1 := by omega
        rw [ancestorValueFuel, if_pos ⟨hg, hk⟩]
        exact hlow q hg hk
    | succ fuel ih =>
        intro q hg hp
        rw [ancestorValueFuel, dif_pos hg]
        by_cases hk : q.totalPsi ≤ 1
        · rw [dif_pos hk]
          exact hlow q hg hk
        · rw [dif_neg hk, hstep q hg (by omega)]
          apply ancestorStep_congr
          intro r hgen hpsi
          exact ih r hgen (by omega)
  exact hf q.totalPsi q hg le_rfl

end AxiomaticGW.SurfaceGenusTwo
