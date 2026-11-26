/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.BelorousskiPandharipande

/-!
# Small complete surface BP polynomials

These fixtures are exact affine equations in ancestors, not invariant values.
Kernel replay binds their full coefficients and queries to all twenty BP
terms, all six assignments and the proved lower-genus algorithms.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBP
open BelorousskiPandharipande

-- Kernel replay of whole equations should not compete for memory.
set_option Elab.async false

/-- Complete collected degree-zero plane equation with states `H,H,1`. -/
def planeZero : RationalTerms (SurfaceAncestorKey .plane) :=
  RationalTerms.term (-6) {⟨2, ![0], {⟨.unit, 0⟩, ⟨.point, 1⟩}, by decide +kernel⟩} +
  RationalTerms.term (6) {⟨2, ![0], {⟨.unit, 1⟩, ⟨.point, 0⟩}, by decide +kernel⟩} +
  RationalTerms.term (-12) {⟨2, ![0], {⟨.point, 0⟩}, by decide +kernel⟩}

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Replay all twenty graph families and all six assignments, without native evaluation.
/-- Every coefficient is checked by the kernel against the executable BP expansion. -/
theorem planeZero_checked : RationalTerms.Equivalent
    (genusTwoTerms .plane 0 0 0 ![.hyperplane, .hyperplane, .unit]) planeZero := by decide +kernel

/-- Complete exceptional-class equation on F₁ with three exceptional states. -/
def exceptional : RationalTerms (SurfaceAncestorKey .hirzebruchOne) :=
  RationalTerms.term (-1/240) 0 +
  RationalTerms.term (12) {⟨2, ![0,0], {⟨.point, 0⟩}, by decide +kernel⟩} +
  RationalTerms.term (-12) {⟨2, ![0,0], {⟨.exceptional 0, 1⟩}, by decide +kernel⟩} +
  RationalTerms.term (-18) {⟨2, ![1,0], {⟨.point, 0⟩, ⟨.exceptional 0, 1⟩}, by decide +kernel⟩} +
  RationalTerms.term (18) {⟨2, ![1,0], {⟨.point, 1⟩, ⟨.exceptional 0, 0⟩}, by decide +kernel⟩}

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Replay full class splittings and signed metric entries, including lower-genus constants.
/-- Every coefficient is checked by the kernel against the executable BP expansion. -/
theorem exceptional_checked : RationalTerms.Equivalent
    (genusTwoTerms .hirzebruchOne 0 ![1,0] 0 (fun _ ↦ .exceptional 0)) exceptional := by
  decide +kernel

/-- On the two-point blowup the class is E₂ and all three states are E₁. -/
def distinctExceptional : RationalTerms (SurfaceAncestorKey .blowupTwo) :=
  RationalTerms.term (-18) {⟨2, ![0,1,0], {⟨.point, 0⟩, ⟨.exceptional 0, 1⟩},
    by decide +kernel⟩} +
  RationalTerms.term (18) {⟨2, ![0,1,0], {⟨.point, 1⟩, ⟨.exceptional 0, 0⟩},
    by decide +kernel⟩}

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Preserve the full exceptional coordinates through every contraction in the replay.
/-- The two exceptional labels and classes remain distinct in the complete equation. -/
theorem distinctExceptional_checked : RationalTerms.Equivalent
    (genusTwoTerms .blowupTwo 0 ![0,1,0] 0 (fun _ ↦ .exceptional 0)) distinctExceptional := by
  decide +kernel

end AxiomaticGW.SurfaceGenusTwoBP
