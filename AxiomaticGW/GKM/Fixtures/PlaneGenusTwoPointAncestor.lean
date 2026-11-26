/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoPointComponents
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsData

/-!
# The degree-one genus-two plane point ancestor of power three

The complete square equation is checked using already certified lower-genus
components. The resulting value belongs to the original ancestor evaluator;
the stable-map descendant still requires its separate mixed comparison.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoPointAncestor
open BelorousskiPandharipande SurfaceGenusTwo PlaneGenusTwoAncestors

set_option maxHeartbeats 4000000 in
-- Check every original graph contraction; only its proved component values are reused.
theorem reduction :
    ancestorReductionTerms (key 12) (by decide +kernel) = terms 12 := by
  rw [← ancestorReductionTermsCached_eq PlaneGenusTwoPointComponents.cache]
  decide +kernel

/-- The unchanged ancestor algorithm returns the exact full boundary sum. -/
theorem value : planeAncestorValueWith GenusTwoPlaneLine.values (key 12) = -9 / 640 := by
  rw [planeAncestorValueWith, ancestorValue_step _ _ (by decide +kernel) (by decide +kernel),
    ancestorStep, reduction]
  change RationalTerms.eval _ terms_12 = _
  norm_num [RationalTerms.eval, terms_12]

end AxiomaticGW.GKM.PlaneGenusTwoPointAncestor
