/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.GenusTwoLocalizationVertex
public import AxiomaticGW.GKM.Fixtures.ExceptionalCoverFactors

/-! # Genus-two source vertices on the exceptional axes of the blowups -/

@[expose] public section
namespace AxiomaticGW.GKM.ExceptionalGenusTwoVertexTransport
open EquivariantCoefficients CurveConventionCertificate ExceptionalCharacterField
open GenusTwoVertexHodgeReduction GenusTwoLocalizationVertex ExceptionalAxisTransport
open CurveReplay.OneBlowup renaming tables → f1
open CurveReplay.TwoBlowups renaming tables → bl2
noncomputable section

/-- The sourced Hodge factor uses the two tangent directions at this vertex and each
outgoing flag's own covering degree. The Boolean selects the target end of the edge. -/
def atEndpoint {X : SurfaceTarget} {v e f : ℕ} (t : Tables X v e) (k : Fin e)
    (last : Bool) (sheets : Fin f → ℕ+) (marks : List ℕ) (seed : ↥seeds → ℚ) : Coefficient :=
  let a := t.edges k
  let p := if last then a.target else a.source
  let w := character a.weight
  reduced seed marks (character (t.tangent p 0)) (character (t.tangent p 1))
    (fun j ↦ (if last then -w else w) / (sheets j).val)

/-- The actual exceptional tangents and all flags transport the complete genus-two vertex
sum at every valence, for arbitrary cotangent powers and any values of the eight seeds. -/
theorem transport (i : Fin 2) {f : ℕ} (last : Bool) (sheets : Fin f → ℕ+)
    (marks : List ℕ) (seed : ↥seeds → ℚ) :
    sector i (atEndpoint f1 2 last sheets marks seed) =
      atEndpoint bl2 (exceptionalEdge i) last sheets marks seed := by
  obtain ⟨hw, _, _, h⟩ := local_field_weights i
  change (sector i).toRingHom _ = _
  cases last <;>
    simp only [atEndpoint, reduced, Bool.false_eq_true, ↓reduceIte, map_source,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_div₀, map_natCast, map_neg, hw,
      (h 0).1, (h 1).1, (h 0).2, (h 1).2]
  exact swap _ _ _ _ _

end
end AxiomaticGW.GKM.ExceptionalGenusTwoVertexTransport
