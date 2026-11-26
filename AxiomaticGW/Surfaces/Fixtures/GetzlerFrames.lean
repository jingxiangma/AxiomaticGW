/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.TermExpansion

/-!
# Fixed low-degree surface Getzler requests

These requests are held independently of the exported candidate coefficients.
They expand the original 33 Getzler columns, including all additional-marking
placements, full curve splittings, and signed node states. All external powers
are zero. The four original markings carry hyperplanes; an added marking
carries the point state.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGetzlerFrames

/-- The line class of the plane, with one additional point insertion. -/
def planeLine : RationalTerms (SurfacePolynomialReduction.Variable .plane) :=
  GetzlerGraphs.primaryTerms .plane 1 ![1] 0 (Option.elim · .point (fun _ ↦ .hyperplane))

/-- The full line class E+F on the one-point blowup. -/
def hirzebruchLine : RationalTerms (SurfacePolynomialReduction.Variable .hirzebruchOne) :=
  GetzlerGraphs.primaryTerms .hirzebruchOne 1 ![1, 1] 0
    (Option.elim · .point (fun _ ↦ .hyperplane))

/-- The full line class E₁+E₂+L on the two-point blowup. -/
def blowupLine : RationalTerms (SurfacePolynomialReduction.Variable .blowupTwo) :=
  GetzlerGraphs.primaryTerms .blowupTwo 1 ![1, 1, 1] 0
    (Option.elim · .point (fun _ ↦ .hyperplane))

/-- The effective reducible class E₁+E₂, with no added markings. -/
def exceptionalSum : RationalTerms (SurfacePolynomialReduction.Variable .blowupTwo) :=
  GetzlerGraphs.primaryTerms .blowupTwo 0 ![1, 1, 0] 0 (fun _ ↦ .hyperplane)

end AxiomaticGW.SurfaceGetzlerFrames
