/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.StrictLineDoubleCoverChain

/-! # Strict-line stable and unstable source vertex regressions -/

public section
namespace AxiomaticGWTest.GKM.StrictLineVertexTransport
open AxiomaticGW AxiomaticGW.GKM EquivariantCoefficients
open StrictLineCoverTransport StrictLineVertexTransport StrictLineDoubleCoverChain
open ExceptionalGenusTwoVertexTransport (atEndpoint)
open ExceptionalGenusTwoVertexValues (seed)
open CurveReplay.OneBlowup renaming tables → f1
open CurveReplay.TwoBlowups renaming tables → bl2

/-- The three flags carry different sheet numbers; the two cotangent powers stay at their marks. -/
theorem mixed_sheets : field (atEndpoint f1 2 true ![1, 3, 2] [0, 2] seed) =
    atEndpoint bl2 3 true ![1, 3, 2] [0, 2] seed := stable ..

/-- A marked two-sheeted end and a rational bivalent node have different signed denominators. -/
theorem unstable_values :
    unstable bl2 3 true (.markedEnd 2 3) = (x/2)^3 / ((-x)*y) ∧
    unstable bl2 3 true (.unmarkedNode 1 1) = 1/((-2*x)*(-x*y)) := by
  have he : euler bl2 3 true = (-x)*y := by
    change ExceptionalCoverFactors.tangent bl2 (bl2.edges 3).target 1 = _
    rw [(tangent_values 1).2, pow_one, pow_one, mul_comm]
  simp only [unstable, flag, ↓reduceIte, he, line_characters.1, PNat.val_ofNat]
  norm_num
  constructor
  · field_simp [x_ne_zero, y_ne_zero]
  · field_simp [x_ne_zero, y_ne_zero]
    ring

/-- The original Sage locus at (11,3) is nonzero and negative, with leaf exchange order two. -/
theorem signed_sample :
    graph.degree = ![0, 0, 2] ∧ ExceptionalDoubleCoverChain.symmetries.card = 2 ∧
    locus = rationalExpression x y ∧ rationalExpression (11 : ℚ) 3 = -107/38720 :=
  ⟨decorated_support.1, decorated_support.2.2, locus_value, by norm_num [rationalExpression]⟩

end AxiomaticGWTest.GKM.StrictLineVertexTransport
