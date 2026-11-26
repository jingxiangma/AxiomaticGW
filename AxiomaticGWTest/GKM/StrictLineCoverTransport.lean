/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.StrictLineCoverTransport

/-! # The degree-two strict-line cover with ordered markings at its two endpoints -/

public section
namespace AxiomaticGWTest.GKM.StrictLineCoverTransport
open AxiomaticGW AxiomaticGW.GKM EquivariantCoefficients StrictLineCoverTransport
open CurveReplay.OneBlowup renaming tables → f1
open CurveReplay.TwoBlowups renaming tables → bl2
open SurfaceFrames.TwoBlowups renaming request → twoFrame

/-- The actual double exceptional cover transported from F₁, in its native orientation. -/
def sourceCover : {G : FixedGraphSupport f1 2 1 //
    G.degree = (2 : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0} :=
  ⟨FixedGraphSupport.singleCover f1 2 2 false, by
    rw [FixedGraphSupport.degree_singleCover]
    decide +kernel⟩

/-- H at the first strict-line endpoint and E₂ at the other have product −x². -/
theorem marked_ends :
    let h := (ofSizeEquiv 2 2 1 sourceCover).val
    twoFrame.restrictions (h.image 0) 1 * twoFrame.restrictions (h.image 1) 3 = -x^2 := by
  dsimp only
  rw [(graph_data 2 sourceCover).2.2 0, (graph_data 2 sourceCover).2.2 1,
    if_pos (by decide +kernel), if_neg (by decide +kernel)]
  change x * (-x) = -x^2
  ring

/-- The interior normal has weight y−x/2; the signed edge factor retains the entire fraction. -/
theorem double_edge :
    ExceptionalCoverFactors.atEdge bl2 3 2 = (4*y-2*x)/x^4 ∧
    field (ExceptionalCoverFactors.atEdge f1 2 2) = (4*y-2*x)/x^4 := by
  rw [cover_factor, and_self, ExceptionalCoverFactors.atEdge, line_characters.1,
    line_characters.2.1]
  unfold ExceptionalCoverFactors.factor ExceptionalCoverFactors.normal
  change ((-1 : Coefficient)^2 / (2 : Coefficient)^2 / (x/2)^4) *
    (∏ j : Fin 1, ((y-x) + (j.val + 1 : Coefficient) * (x/2))) = _
  rw [Fin.prod_univ_one]
  norm_num
  field_simp [x_ne_zero]
  ring

end AxiomaticGWTest.GKM.StrictLineCoverTransport
