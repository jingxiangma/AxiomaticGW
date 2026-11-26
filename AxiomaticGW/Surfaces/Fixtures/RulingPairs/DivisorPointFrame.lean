/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Transfer
public import AxiomaticGW.Surfaces.GenusTwoPairTerms
public import AxiomaticGW.Surfaces.GenusTwoPulledSquare
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPositiveDivisorPairs

/-! # The two genus-two divisor–point interior shapes on the rulings of Bl₂

The primary point with a second descendant of a divisor uses a pulled
cotangent square. With a first descendant on both markings it uses the
two-marking product. Both orders keep the entire mixed calibration.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingDivisorPoint
open BlowupTwoRuling (X curve label)
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants SurfaceGenusTwoPositiveDivisorPairs
open BlowupTwoDoubleLine (terminals terminals_eq)

/-- H, the exceptional component, and the exceptional divisor meeting the moving fiber. -/
def divisor (i : Fin 2) (j : Fin 3) : SurfaceBasisLabel X :=
  ![.hyperplane, .exceptional i, .exceptional i.rev] j

/-- Divisor in the selected shape, with one or two cotangent powers. -/
def divMark (i : Fin 2) (j : Fin 3) (square : Bool) : SurfaceInsertion X :=
  ⟨divisor i j, if square then 2 else 1⟩

/-- Primary point in the square relation or first descendant in the product relation. -/
def ptMark (square : Bool) : SurfaceInsertion X := ⟨.point, if square then 0 else 1⟩

/-- Each full two-marking request, with the point first exactly when indicated. -/
def request (i : Fin 2) (j : Fin 3) (square pointFirst : Bool) : SurfaceQuery X :=
  let d := divMark i j square
  let p := ptMark square
  ⟨2, curve i, if pointFirst then [p, d] else [d, p]⟩

/-- Leading ancestor key, whose marking multiset is independent of the incoming order. -/
def leading (i : Fin 2) (j : Fin 3) (square : Bool) : SurfaceAncestorKey X :=
  pairKey (curve i) (divMark i j square) (ptMark square)

/-- The proper-class keys that can occur in these two calibrated shapes. -/
def tailKey (i : Fin 2) : Fin 21 → SurfaceAncestorKey X :=
  let e := X.exceptionalCurve i
  let l := BlowupTwoLineBP.line
  let d (j : Fin 5) (p : ℕ) : SurfaceInsertion X := ⟨label i j, p⟩
  ![pairKey 0 (d 0 0) (d 4 1),
    pairKey 0 (d 1 0) (d 4 0),
    pairKey 0 (d 1 0) (d 1 1),
    pairKey 0 (d 1 0) (d 2 1),
    pairKey 0 (d 1 0) (d 3 1),
    pairKey 0 (d 2 0) (d 4 0),
    pairKey 0 (d 3 0) (d 4 0),
    pairKey 0 (d 3 0) (d 1 1),
    pairKey 0 (d 3 0) (d 2 1),
    pairKey 0 (d 3 0) (d 3 1),
    pairKey 0 (d 4 0) (d 0 1),
    pairKey e (d 1 0) (d 4 1),
    pairKey e (d 2 0) (d 4 1),
    pairKey e (d 3 0) (d 4 1),
    pairKey e (d 4 0) (d 4 0),
    pairKey e (d 4 0) (d 1 1),
    pairKey e (d 4 0) (d 2 1),
    pairKey e (d 4 0) (d 3 1),
    pairKey l (d 2 0) (d 4 1),
    pairKey l (d 4 0) (d 4 0),
    pairKey l (d 4 0) (d 2 1)]

/-- Original signed proper terms, with repeated curve classes distinguished by their keys. -/
def row (square : Bool) (j : Fin 3) : List (ℚ × Fin 21) :=
  if square then ![[(1, 6), (1, 10), (1, 14), (1, 15), (-1, 16), (-1, 17)],
    [(-1, 1), (1, 5), (1, 6), (1, 14), (1, 15), (-1, 16), (-1, 17), (-1, 19), (-1, 20)],
    [(1, 1), (1, 10), (1, 14), (1, 15), (-1, 16), (-1, 17)]] j
  else ![[(1, 0), (1, 2), (-1, 7), (1, 11), (-1, 12), (-1, 13)],
    [(1, 3), (-1, 8), (1, 11), (-1, 12), (-1, 13), (-1, 18)],
    [(1, 0), (1, 4), (-1, 9), (1, 11), (-1, 12), (-1, 13)]] j

/-- In both orders the original descendant is its leading ancestor and the signed proper terms. -/
theorem query_eq (i : Fin 2) (j : Fin 3) (square pointFirst : Bool) :
    queryValue? 0 (request i j square pointFirst) =
      some (ancestorValueWith terminals (leading i j square) +
        ((row square j).map fun t ↦ t.1 * ancestorValueWith terminals (tailKey i t.2)).sum) := by
  have hp (a b : SurfaceInsertion X) (h : (a, b) =
      (if pointFirst then ptMark square else divMark i j square,
       if pointFirst then divMark i j square else ptMark square)) :
      pairMixed (curve i) a b =
        RationalTerms.term 1 {leading i j square} + pairExpression (tailKey i) (row square j) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    fin_cases i <;> fin_cases j <;> cases square <;> cases pointFirst <;> decide +kernel
  have hβ : X.effective.energy (request i j square pointFirst).beta ≤ 2 := by
    change X.effective.energy (curve i) ≤ 2
    fin_cases i <;> decide +kernel
  rw [← queryValueWith?_eq_of_table 0 2 terminals (fun s _ ↦ terminals_eq s) _ hβ]
  cases pointFirst <;> simp only [request, Bool.false_eq_true, if_false, if_true] at hp ⊢ <;>
    rw [queryValueWith?_pair, hp _ _ rfl, RationalTerms.eval_add,
    RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton, map_one, one_mul,
    eval_pairExpression]

end AxiomaticGW.BlowupTwoRulingDivisorPoint
