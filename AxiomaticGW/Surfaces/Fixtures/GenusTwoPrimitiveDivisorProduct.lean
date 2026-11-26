/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoDivisorProductHead
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoDivisorProductLower

/-! # The two-divisor descendant product at anticanonical degree one

For two first descendants of divisors, the original evaluator gives the product
of the two curve pairings divided by 144, plus three times their intersection
form times the reconstructed first descendant of a point in the same class.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open SurfaceFirstDescendant
variable {X : SurfaceTarget}

private abbrev doubleKey (beta : X.Curve) (a b : SurfaceBasisLabel X) :=
  pairKey beta ⟨a, 1⟩ ⟨b, 1⟩

private theorem no_square (a b : SurfaceBasisLabel X) :
    ¬ (squareMarks (doubleKey 0 a b)).Nonempty := by
  revert a b
  cases X <;> decide +kernel

private def selected (a b : SurfaceBasisLabel X) : SurfaceBasisLabel X × SurfaceBasisLabel X :=
  let q := doubleKey 0 a b
  let hk : 1 < q.totalPsi := by change 1 < 1 + 1 + 0; decide
  (q.orderedLabels (firstProductMark q hk),
    q.orderedLabels (secondProductMark q hk (no_square a b)))

private theorem selected_perm (a b : SurfaceBasisLabel X) :
    (selected a b = (a, b)) ∨ (selected a b = (b, a)) := by
  revert a b
  cases X <;> decide +kernel

/-- The complete primitive two-divisor formula, with both geometric intersections
and the original same-class point state, for either order of the two markings. -/
theorem queryValue?_primitiveDivisorProduct (i : Fin X.blowups) (beta : X.Curve)
    (he : X.effective.energy beta = 1) (a b : SurfaceBasisLabel X)
    (ha : a.codimension = 1) (hb : b.codimension = 1) :
    SurfaceGenusTwoBlowupDescendants.queryValue? i ⟨2, beta, [⟨a, 1⟩, ⟨b, 1⟩]⟩ =
      some (a.primaryFactor beta * b.primaryFactor beta / 144 +
        3 * divisorIntersection a b * SurfaceGenusTwoBlowupRecursion.values i (beta, .point)) := by
  rw [queryValue?_firstDivisorPair i beta he a b ha hb]
  apply congrArg some
  let q := doubleKey beta a b
  let v := SurfaceGenusTwoBlowupLowPsi.ancestorValue i
  let d := selected a b
  have hd : d.1.codimension = 1 ∧ d.2.codimension = 1 := by
    rcases selected_perm a b with h | h <;> rw [show d = _ from h]
    · exact ⟨ha, hb⟩
    · exact ⟨hb, ha⟩
  have hn : q.orderedInsertions.length = 2 := by rw [q.orderedInsertions_length]; rfl
  have hp : q.totalPsi = 2 := rfl
  have hs : ¬ (squareMarks q).Nonempty := no_square a b
  change ancestorValue v q = _
  have hhead : productGraph (productVertex v) q.beta ![d.1, d.2] 0 = _ :=
    divisorProductHead_value i beta he d.1 d.2 hd.1 hd.2
  have hlower : (∑ j : Fin 24, productGraph (productVertex v) q.beta ![d.1, d.2] j.succ) = _ :=
    SurfaceGenusTwoDivisorProductLower.sum_eq v beta he d.1 d.2 hd.1 hd.2
  rw [ancestorValue_twoMarking_product v q rfl hn hp hs ![d.1, d.2] rfl rfl,
    Fin.sum_univ_succ, hhead, hlower]
  have hcomm : divisorIntersection b a = divisorIntersection a b := by
    by_cases h : a = b
    · rw [h]
    · simp only [divisorIntersection, if_neg h, if_neg (Ne.symm h)]
  rcases selected_perm a b with h | h <;> rw [show d = _ from h]
  · ring
  · rw [hcomm]
    ring

end AxiomaticGW.SurfaceGenusTwo
