/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.InteriorDomain
public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.ProperFrame
public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Transfer

/-! # Exact mixed transfer of every two-marked interior request on the two rulings

Each row keeps its full-class ancestor and every signed occurrence at the
constant, exceptional and strict-line subclasses. The row is checked in both
orders against the original mixed descendant polynomial before evaluation.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingInterior
open BlowupTwoRuling (X curve label)
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoDoubleLine (terminals terminals_eq)

/-- The unique full-class monomial indexed by the raised and unraised insertions. -/
def leading (i : Fin 2) (a b : Fin 5) : SurfaceAncestorKey X :=
  pairKey (curve i) (insertion (label i a) true) (insertion (label i b) false)

/-- Signed proper monomials, with coefficients repeated when the original transfer repeats them. -/
def coefficients (a b : Fin 5) : List (ℚ × Fin 68) :=
  (#[
    [(-1, 4), (2, 5), (1, 7), (-2, 9), (-2, 10), (2, 10), (1, 11), (-1, 12), (-1, 12), (-1, 13),
    (1, 14), (-2, 15), (-1, 17), (-1, 24), (-1, 29), (1, 34), (1, 39), (-2, 44), (-1, 48),
    (1, 51), (1, 53), (-1, 58), (-2, 63), (-1, 67)],
    [(1, 4), (-2, 5), (-2, 6), (-1, 7), (2, 10), (1, 11), (1, 12), (2, 15), (1, 17), (-1, 21),
    (1, 29), (-1, 34), (-1, 39), (-2, 41), (-1, 45), (1, 46), (1, 47), (-2, 60), (-1, 64)],
    [(-2, 5), (-2, 7), (-1, 7), (2, 10), (2, 10), (1, 11), (-1, 12), (1, 12), (1, 12), (-1, 13),
    (2, 15), (1, 17), (-1, 22), (1, 29), (-1, 34), (-1, 39), (-2, 42), (-1, 46), (1, 49),
    (1, 50), (-1, 58), (-2, 61), (-1, 65)],
    [(1, 4), (-2, 5), (-1, 7), (-2, 8), (2, 10), (1, 12), (1, 13), (2, 15), (1, 17), (-1, 23),
    (1, 29), (-1, 34), (-1, 39), (-2, 43), (-1, 47), (1, 50), (1, 52), (-2, 62), (-1, 66)],
    [(-2, 5), (1, 10), (-1, 20), (-2, 40), (-1, 41), (1, 42), (1, 43), (-2, 59), (-1, 61)],
    [(-1, 1), (-1, 10), (-1, 11), (1, 12), (1, 13), (1, 19), (1, 24), (-1, 26), (1, 31),
    (1, 36), (1, 44), (1, 48), (-1, 51), (-1, 53), (-1, 55)],
    [(1, 1), (1, 16), (1, 21), (1, 26), (-1, 31), (-1, 36), (1, 41), (1, 45), (-1, 46), (-1, 47)],
    [(-1, 10), (-1, 11), (1, 12), (1, 13), (1, 17), (1, 22), (1, 26), (-1, 31), (-1, 36),
    (1, 42), (1, 46), (-1, 49), (-1, 50), (-1, 55)],
    [(1, 1), (1, 18), (1, 23), (1, 26), (-1, 31), (-1, 36), (1, 43), (1, 47), (-1, 50), (-1, 52)],
    [(1, 15), (1, 20), (1, 40), (1, 41), (-1, 42), (-1, 43)],
    [(-1, 2), (1, 5), (1, 7), (-1, 9), (-1, 10), (-1, 10), (-1, 11), (-1, 12), (1, 12), (1, 13),
    (1, 14), (-1, 15), (-1, 17), (1, 19), (-1, 27), (1, 32), (1, 37), (1, 44), (1, 48),
    (-1, 51), (-1, 53), (-1, 56), (-1, 63), (-1, 67)],
    [(1, 2), (-1, 5), (-1, 6), (-1, 7), (1, 10), (1, 11), (1, 12), (1, 15), (1, 16), (1, 17),
    (1, 27), (-1, 32), (-1, 37), (1, 41), (1, 45), (-1, 46), (-1, 47), (-1, 60), (-1, 64)],
    [(-1, 5), (-1, 7), (-1, 7), (-1, 10), (1, 10), (-1, 11), (1, 12), (1, 12), (1, 12), (1, 13),
    (1, 15), (1, 17), (1, 17), (1, 27), (-1, 32), (-1, 37), (1, 42), (1, 46), (-1, 49),
    (-1, 50), (-1, 56), (-1, 61), (-1, 65)],
    [(1, 2), (-1, 5), (-1, 7), (-1, 8), (1, 10), (1, 12), (1, 13), (1, 15), (1, 17), (1, 18),
    (1, 27), (-1, 32), (-1, 37), (1, 43), (1, 47), (-1, 50), (-1, 52), (-1, 62), (-1, 66)],
    [(-1, 5), (1, 10), (1, 15), (1, 40), (1, 41), (-1, 42), (-1, 43), (-1, 59), (-1, 61)],
    [(-1, 3), (1, 9), (-1, 10), (-1, 11), (1, 12), (1, 13), (1, 24), (-1, 28), (1, 33), (1, 38),
    (1, 44), (1, 48), (-1, 51), (-1, 53), (-1, 57)],
    [(1, 3), (1, 6), (1, 21), (1, 28), (-1, 33), (-1, 38), (1, 41), (1, 45), (-1, 46), (-1, 47)],
    [(1, 7), (-1, 10), (-1, 11), (1, 12), (1, 13), (1, 22), (1, 28), (-1, 33), (-1, 38),
    (1, 42), (1, 46), (-1, 49), (-1, 50), (-1, 57)],
    [(1, 3), (1, 8), (1, 23), (1, 28), (-1, 33), (-1, 38), (1, 43), (1, 47), (-1, 50), (-1, 52)],
    [(1, 5), (1, 20), (1, 40), (1, 41), (-1, 42), (-1, 43)],
    [(-1, 0), (1, 9), (-1, 19), (-1, 25), (1, 30), (1, 35), (-1, 54)],
    [(1, 0), (1, 6), (-1, 16), (1, 25), (-1, 30), (-1, 35)],
    [(1, 7), (-1, 17), (1, 25), (-1, 30), (-1, 35), (-1, 54)],
    [(1, 0), (1, 8), (-1, 18), (1, 25), (-1, 30), (-1, 35)],
    [(1, 5), (-1, 15)]] : Array (List (ℚ × Fin 68)))[5*a.val+b.val]'(by
    have := a.isLt
    have := b.isLt
    change _ < 25
    omega)

set_option maxHeartbeats 2400000 in
-- All one hundred full-coordinate marked polynomials are verified independently.
/-- Original mixed calibration for any of the hundred ordered interior queries. -/
theorem query_eq (i : Fin 2) (a b : Fin 5) (raisedFirst : Bool) :
    queryValue? 0 (request i (label i a) (label i b) raisedFirst) =
      some (ancestorValueWith terminals (leading i a b) +
        ((coefficients a b).map fun t ↦ t.1 *
          ancestorValueWith terminals (properKey i t.2)).sum) := by
  let u := insertion (label i a) true
  let v := insertion (label i b) false
  have hp (x y : SurfaceInsertion X) (h : (x, y) =
      (if raisedFirst then u else v, if raisedFirst then v else u)) :
      pairMixed (curve i) x y =
        RationalTerms.term 1 {leading i a b} + pairExpression (properKey i) (coefficients a b) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    fin_cases i <;> fin_cases a <;> fin_cases b <;> cases raisedFirst <;> decide +kernel
  have hβ : X.effective.energy (request i (label i a) (label i b) raisedFirst).beta ≤ 2 := by
    change X.effective.energy (curve i) ≤ 2
    fin_cases i <;> decide +kernel
  rw [← queryValueWith?_eq_of_table 0 2 terminals (fun s _ ↦ terminals_eq s) _ hβ]
  cases raisedFirst <;> simp only [request, Bool.false_eq_true, if_false, if_true] at hp ⊢ <;>
    rw [queryValueWith?_pair, hp _ _ rfl, RationalTerms.eval_add, RationalTerms.eval_term,
      Multiset.map_singleton, Multiset.prod_singleton, map_one, one_mul, eval_pairExpression]

end AxiomaticGW.BlowupTwoRulingInterior
