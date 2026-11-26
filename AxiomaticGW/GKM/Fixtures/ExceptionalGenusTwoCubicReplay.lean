/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalGenusTwoCubic
public import AxiomaticGW.GKM.Fixtures.ExceptionalCharacterField
public import AxiomaticGW.GKM.Fixtures.ExceptionalBoundaryClass
public import AxiomaticGW.GKM.Fixtures.ExceptionalDegreeOneLoci

/-! # The cubic descendant on the three exceptional axes of the fixed targets

Transport commutes with each Hodge term, the edge and tangent factors, and the
unstable rational vertex. The first elliptic split is killed by the marked vertex.
The ordered native edge uses the same source/target convention on all three axes.
-/

@[expose] public noncomputable section
namespace AxiomaticGW.GKM.ExceptionalGenusTwoCubicReplay
open EquivariantCoefficients ExceptionalGenusTwoCubic ExceptionalBoundaryData
open ExceptionalBoundaryClass (target beta own)

/-- The exact request for the own exceptional class on the corresponding surface. -/
def requests (c : Case) : SurfaceQuery (target c) :=
  ⟨2, beta c, [⟨.exceptional (own c), 3⟩]⟩

/-- Change to the pinned variables at the two endpoints. -/
def characters : Case → Coefficient ≃+* Coefficient
  | .f1 | .first => RingEquiv.refl _
  | .second => ExceptionalCharacterField.field

/-- The actual edge and tangent coefficients on each target come from the held bridge table. -/
theorem bridge (c : Case) : characters c ((factors .first).edge * (factors .first).tangent) =
    (factors c).edge * (factors c).tangent := by
  cases c with
  | f1 | first => rfl
  | second =>
    exact ExceptionalCharacterField.bridge_edge_tangent 1

/-- All Hodge coefficients are rational, so transport changes only the torus characters. -/
theorem map_stableVertex (c : Case) (m : Bool) (w t : Coefficient) :
    characters c (stableVertex m w t) = stableVertex m (characters c w) (characters c t) := by
  simp only [stableVertex, map_sum, map_div₀, map_mul, map_zpow₀, map_pow, map_ratCast]

private theorem map_atEnds (c : Case) (m : Bool) (w t u : Coefficient) :
    characters c (atEnds m w t u) =
    (factors c).edge * (factors c).tangent * (if m then characters c t else characters c u) *
      stableVertex m (characters c w) (characters c t) *
      ((if m then -(characters c w) else (-(-(characters c w))) ^ 3) /
        ((-(characters c w)) * characters c u)) := by
  rw [← bridge c]
  cases m <;> simp only [atEnds, Bool.false_eq_true, if_false, if_true, map_mul,
    map_stableVertex, map_div₀, map_neg, map_pow]

/-- The contributions on the requested target use its own native edge and tangent factors. -/
def locus (c : Case) (g : Fin 3) (m : Fin 2) : Coefficient :=
  if g = 1 then 0 else
  let w := characters c (if g = 2 then x - y else y - x)
  let t := characters c (if g = 2 then y else x)
  let u := characters c (if g = 2 then x else y)
  let marked := decide ((g = 2 ∧ m = 0) ∨ (g = 0 ∧ m = 1))
  (factors c).edge * (factors c).tangent * (if marked then t else u) * stableVertex marked w t *
    ((if marked then -w else (-(-w)) ^ 3) / ((-w) * u))

/-- Character change intertwines each of the six separate contributions. -/
theorem locus_eq (c : Case) (g : Fin 3) (m : Fin 2) :
    characters c (contribution g m) = locus c g m := by
  unfold contribution locus
  split
  · exact map_zero _
  · exact map_atEnds c _ _ _ _

/-- The full nonconstant coefficient in the pinned character convention. -/
def equivariant : Case → Coefficient
  | .f1 | .first => (x + y) / 240
  | .second => (y - 2*x) / 240

/-- All possible genus and marked-end choices are summed, with the two elliptic splits zero. -/
theorem sum_loci (c : Case) : (∑ g : Fin 3, ∑ m : Fin 2, locus c g m) = equivariant c := by
  have h : (∑ g : Fin 3, ∑ m : Fin 2, locus c g m) =
      characters c (∑ g : Fin 3, ∑ m : Fin 2, contribution g m) := by
    simp only [map_sum, locus_eq]
  rw [h]
  rw [ExceptionalGenusTwoCubic.sum_loci]
  cases c with
  | f1 | first => rfl
  | second =>
    change ExceptionalCharacterField.field ((x+y)/240) = (y-2*x)/240
    rw [map_div₀, map_add, map_ofNat, ExceptionalCharacterField.field_generators.1,
      ExceptionalCharacterField.field_generators.2]
    ring

/-- The six-locus sum on any labeled degree-one E₁ support, counted by its arithmetic
genus decorations and its marked vertex. -/
theorem sum_on_support {v e : ℕ} (G : FixedGraphSupport CurveReplay.TwoBlowups.tables v e)
    (hd : G.degree = ![1, 0, 0])
    [Fintype (ExceptionalDegreeOneLoci.Decoration v e)] :
    (∑ z : ExceptionalDegreeOneLoci.Decoration v e,
      let k := ExceptionalDegreeOneLoci.decorationEquiv G hd z
      locus .first k.1 k.2) = equivariant .first := by
  rw [(ExceptionalDegreeOneLoci.decorationEquiv G hd).sum_comp
    (fun k ↦ locus .first k.1 k.2), Fintype.sum_prod_type]
  exact sum_loci .first

/-- Each ordinary zero follows from the signed dimension rule without numerical seeds. -/
theorem ordinary (c : Case) : (requests c).dimensionVanishing? = some 0 := by
  cases c <;> decide +kernel

end AxiomaticGW.GKM.ExceptionalGenusTwoCubicReplay
