/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.StrictLineVertexTransport
public import AxiomaticGW.GKM.Fixtures.ExceptionalDoubleCoverChain

/-! # A signed bivalent genus-two locus in class 2L

The two unramified edges meet a genus-two component carrying τ₃(E₂) at fixed point 3.
The rational leaves both map to point 2. Their simultaneous exchange has order two.
-/

@[expose] public section
namespace AxiomaticGW.GKM.StrictLineDoubleCoverChain
open CurveConventionCertificate EquivariantCoefficients StrictLineCoverTransport
open StrictLineVertexTransport (unstable flag euler branches tangent_values)
open ExceptionalDoubleCoverChain (support symmetries leaf_exchange center center_eq)
open ExceptionalGenusTwoVertexTransport (atEndpoint)
open ExceptionalGenusTwoVertexValues (seed)
open ExceptionalCoverFactors (atEdge tangent)
open CurveReplay.TwoBlowups renaming tables → bl2
open SurfaceFrames.TwoBlowups renaming request → twoFrame

abbrev graph := support bl2 3

/-- Valence is read from the two source edges, including both occurrences at the marked center. -/
def valence (w : Fin 3) : ℕ :=
  (Finset.univ.filter fun p : Fin 2 × Fin 2 ↦ graph.endpoint p.1 p.2 = w).card

theorem decorated_support : graph.degree = ![0, 0, 2] ∧ (∀ w, valence w = ![1, 2, 1] w) ∧
    symmetries.card = 2 := ⟨by decide +kernel, by decide +kernel, leaf_exchange.2⟩

noncomputable section

private theorem edge : atEdge bl2 3 1 = -1/x^2 := by
  rw [atEdge, line_characters.1, line_characters.2.1]
  have h : ExceptionalCoverFactors.normal 1 x (y-x) = 1 := by
    unfold ExceptionalCoverFactors.normal
    apply Finset.prod_eq_one
    intro i _
    exact Fin.elim0 i
  rw [ExceptionalCoverFactors.factor, h, mul_one]
  norm_num

/-- Source factor of either unmarked rational leaf in the native strict-line coordinates. -/
theorem leaf : unstable bl2 3 false (.unmarkedEnd 1) = x / (x*(y-x)) := by
  simp only [unstable, flag, euler, Bool.false_eq_true, ↓reduceIte, line_characters.1,
    (tangent_values 1).1, pow_one]
  norm_num

/-- The native endpoint uses tangent weights in the opposite order to the marked center. -/
theorem bivalent :
    atEndpoint bl2 3 true (fun _ : Fin 2 ↦ 1) [3] seed = center [3] (-x) y := by
  simp only [atEndpoint, center, GenusTwoLocalizationVertex.reduced, ↓reduceIte,
    branches.2.2.1, branches.2.2.2, line_characters.1, PNat.val_ofNat, Nat.cast_one, div_one]
  exact GenusTwoLocalizationVertex.swap _ _ _ _ _

/-- Assemble both edges and leaves with a specified center integral and the native insertion. -/
def withCenter (middle : Coefficient) : Coefficient :=
  (∏ e, atEdge bl2 (graph.edgeIndex e) (graph.cover e)) *
    (∏ w, tangent bl2 (graph.image w) (valence w)) *
    (twoFrame.restrictions (graph.image 1) 3) *
    (unstable bl2 3 false (.unmarkedEnd (graph.cover 0)) *
      middle *
      unstable bl2 3 false (.unmarkedEnd (graph.cover 1))) / symmetries.card

/-- The native center gives the signed source locus with its automorphism denominator. -/
def locus : Coefficient := withCenter (atEndpoint bl2 3 true graph.cover [3] seed)

/-- Rational expression for the two-character locus, also usable at regular numerical samples. -/
def rationalExpression {K : Type*} [Field K] (u v : K) : K :=
  -11*v^3/(1440*u^3) - 103*v^2/(5760*u^2) - 3*v/(640*u)

/-- Exact signed contribution of this individual locus before summing the 2L localization frame. -/
theorem locus_value : locus = rationalExpression x y := by
  unfold locus withCenter rationalExpression
  rw [Fin.prod_univ_two, Fin.prod_univ_three, leaf_exchange.2]
  simp only [decorated_support.2.1]
  change ((atEdge bl2 3 1 * atEdge bl2 3 1) *
    (tangent bl2 (bl2.edges 3).source 1 * tangent bl2 (bl2.edges 3).target 2 *
      tangent bl2 (bl2.edges 3).source 1) * (-x) *
    (unstable bl2 3 false (.unmarkedEnd 1) *
      atEndpoint bl2 3 true (fun _ : Fin 2 ↦ 1) [3] seed *
      unstable bl2 3 false (.unmarkedEnd 1))) / (2 : Coefficient) = _
  rw [edge, (tangent_values 1).1, (tangent_values 2).2, leaf, bivalent,
    (center_eq (-x) y (neg_ne_zero.mpr x_ne_zero) y_ne_zero).1]
  field_simp [x_ne_zero, y_ne_zero, y_sub_x_ne_zero]
  ring

end
end AxiomaticGW.GKM.StrictLineDoubleCoverChain
