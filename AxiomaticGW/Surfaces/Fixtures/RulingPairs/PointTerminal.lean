/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.Transfer
public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.ProperLow

/-! # The two point–point orders at each ruling are the original P terminal -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingInterior
open BlowupTwoRuling (X curve label)
open BlowupTwoDoubleLine (terminals terminals_eq)
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants SurfaceGenusTwoBlowupOrder
open SurfacePolynomialReduction

/-- The two constant-class proper terms vanish, leaving precisely the ruling P state. -/
theorem point_point (i : Fin 2) (raisedFirst : Bool) :
    queryValue? 0 (request i .point .point raisedFirst) =
      some (SurfaceGenusTwoBlowupRecursion.values 0 (curve i, .point)) := by
  change queryValue? 0 (request i (label i 4) (label i 4) raisedFirst) = _
  rw [query_eq]
  have ht : coefficients 4 4 = [(1, lowIndex 1), (-1, lowIndex 9)] := by decide +kernel
  rw [ht]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, proper_low_values, mul_zero,
    add_zero]
  rw [ancestorValueWith, ancestorValue_low _ _ rfl (by fin_cases i <;> decide +kernel),
    SurfaceGenusTwoBlowupLowPsi.ancestorValueWith]
  have hn : normalizedTerms (leading i 4 4) = RationalTerms.term 1
      {Sum.inr (Family.point.query (curve i))} := by
    fin_cases i <;> decide +kernel
  rw [hn]
  simp only [RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton, map_one,
    one_mul, canonicalValuation_query, terminals_eq]

end AxiomaticGW.BlowupTwoRulingInterior
