/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoAncestorCertificate
public import AxiomaticGW.Surfaces.GenusTwoPrimitivePairTransfer
public import AxiomaticGW.Surfaces.GenusTwoBlowupQueryCertificate

/-! # First descendants of two divisors in anticanonical degree one

Both positive-tail terms are kept in the mixed transfer. At a divisor pair
their class-zero ancestors vanish in the original blowup normalization.
Consequently the descendant equals its two-marked ancestor.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open SurfaceGenusTwoBlowupOrder SurfaceDescendant
variable {X : SurfaceTarget}

private def boundaryTable (s : State X) : ℚ :=
  SurfaceGenusTwoBlowupBoundary.value s.1 s.2

private theorem boundaryTable_zero (i : Fin X.blowups) (s : State X)
    (he : X.effective.energy s.1 ≤ 0) :
    boundaryTable s = SurfaceGenusTwoBlowupRecursion.values i s := by
  have hz := (X.effective.energy_eq_zero_iff s.1).mp (by omega)
  exact (SurfaceGenusTwoBlowupRecursion.values_boundary i s (by rw [hz, map_zero])).symm

private theorem low_zero (a b : SurfaceBasisLabel X) (hb : b.codimension = 1) :
    SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundaryTable
      (pairKey (X := X) 0 ⟨a, 0⟩ ⟨b, 1⟩) = 0 := by
  revert a b
  cases X <;> decide +kernel

private theorem ancestor_zero (i : Fin X.blowups) (a b : SurfaceBasisLabel X)
    (hb : b.codimension = 1) : SurfaceGenusTwoBlowupDescendants.ancestorValue i
      (pairKey 0 ⟨a, 0⟩ ⟨b, 1⟩) = 0 := by
  let q := pairKey (X := X) 0 ⟨a, 0⟩ ⟨b, 1⟩
  rw [← SurfaceGenusTwoBlowupDescendants.ancestorValueWith_eq_of_table i 0 boundaryTable
    (boundaryTable_zero i) q rfl (by change X.effective.energy 0 ≤ 0; rw [map_zero])]
  unfold SurfaceGenusTwoBlowupDescendants.ancestorValueWith
  rw [ancestorValue_low _ q rfl (by change 0 + 1 + 0 ≤ 1; decide)]
  exact low_zero a b hb

private theorem pairKey_swap (beta : X.Curve) (a b : SurfaceInsertion X) :
    pairKey beta a b = pairKey beta b a := by
  apply (SurfaceAncestorKey.eq_iff _ _).mpr
  exact ⟨rfl, rfl, Multiset.pair_comm a b⟩

/-- Each calibration correction is zero after the full low-power normalization.
The coefficient of the positive tail may itself be nonzero. -/
theorem eval_firstPairTails (i : Fin X.blowups) (beta : X.Curve) (a b : SurfaceBasisLabel X)
    (ha : a.codimension = 1) (hb : b.codimension = 1) :
    RationalTerms.eval (SurfaceGenusTwoBlowupDescendants.ancestorValue i)
      (firstPairTails beta a b) = 0 := by
  have hz (c : SurfaceBasisLabel X) :
      SurfaceGenusTwoBlowupDescendants.ancestorValue i (pairKey 0 ⟨a, 1⟩ ⟨c, 0⟩) = 0 := by
    rw [pairKey_swap]
    exact ancestor_zero i c a ha
  simp only [firstPairTails, RationalTerms.eval_add, RationalTerms.eval_sum,
    RationalTerms.eval_scale, RationalTerms.eval_term, Algebra.algebraMap_self_apply,
    Multiset.map_singleton, Multiset.prod_singleton, hz, ancestor_zero i _ b hb,
    mul_zero, Finset.sum_const_zero, add_zero]

/-- In energy one the original stable-map divisor pair equals the two-marked
ancestor in the same full class. Both divisor labels and their marking order are retained. -/
theorem queryValue?_firstDivisorPair (i : Fin X.blowups) (beta : X.Curve)
    (he : X.effective.energy beta = 1) (a b : SurfaceBasisLabel X)
    (ha : a.codimension = 1) (hb : b.codimension = 1) :
    SurfaceGenusTwoBlowupDescendants.queryValue? i ⟨2, beta, [⟨a, 1⟩, ⟨b, 1⟩]⟩ =
      some (SurfaceGenusTwoBlowupDescendants.ancestorValue i
        (pairKey beta ⟨a, 1⟩ ⟨b, 1⟩)) := by
  let q : SurfaceQuery X := ⟨2, beta, [⟨a, 1⟩, ⟨b, 1⟩]⟩
  let l : Fin 2 → SurfaceBasisLabel X := fun j ↦ (q.insertions.get j).label
  have hd : (fun j : Fin 2 ↦ (q.insertions.get j).psi) = (fun _ ↦ 1) := by
    funext j
    fin_cases j <;> rfl
  change some (RationalTerms.eval (SurfaceGenusTwoBlowupDescendants.ancestorValue i)
    (mixedAncestorTerms 2 (Fin 2) _ (List.finRange 2) beta
      (fun j : Fin 2 ↦ (q.insertions.get j).psi) 0 l)) = _
  rw [hd, mixed_firstPair_primitive beta he, RationalTerms.eval_add,
    eval_firstPairTails i beta (l 0) (l 1) ha hb]
  simp only [RationalTerms.eval_term, Algebra.algebraMap_self_apply, Multiset.map_singleton,
    Multiset.prod_singleton, one_mul, add_zero]
  rfl

end AxiomaticGW.SurfaceGenusTwo
