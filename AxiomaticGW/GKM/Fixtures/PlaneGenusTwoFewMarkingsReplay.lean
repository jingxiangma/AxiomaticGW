/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsOnePoint
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsUnit
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsHyperplane
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsPoint
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine

/-!
# Complete native plane genus-two few-marking replay

The separately checked arithmetic covers all 48 held queries.
The candidate canonical table is identified with the accepted line table
before its soundness theorem certifies the original descendant algorithm.
This does not certify equivariant localization or import CohFT classes.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536
set_option cbv.maxSteps 4000000

namespace AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay

open BelorousskiPandharipande

/-- Candidate arithmetic uses exactly the separately accepted canonical table. -/
theorem canonicalValues_eq : canonicalValues = GenusTwoPlaneLine.values := rfl

/-- Complete evaluation of every held request, with no added numerical seed. -/
theorem computed (i : Fin 48) : planeQueryValueWith? GenusTwoPlaneLine.values
    (requests i) = some (values i) := by
  rw [← canonicalValues_eq]
  fin_cases i
  · exact OnePoint.computed 0
  · exact OnePoint.computed 1
  · exact OnePoint.computed 2
  · exact Unit.computed 0
  · exact Unit.computed 1
  · exact Unit.computed 2
  · exact Unit.computed 3
  · exact Unit.computed 4
  · exact Unit.computed 5
  · exact Unit.computed 6
  · exact Unit.computed 7
  · exact Unit.computed 8
  · exact Unit.computed 9
  · exact Unit.computed 10
  · exact Unit.computed 11
  · exact Unit.computed 12
  · exact Unit.computed 13
  · exact Unit.computed 14
  · exact Unit.computed 15
  · exact Unit.computed 16
  · exact Unit.computed 17
  · exact Hyperplane.computed 0
  · exact Hyperplane.computed 1
  · exact Hyperplane.computed 2
  · exact Hyperplane.computed 3
  · exact Hyperplane.computed 4
  · exact Hyperplane.computed 5
  · exact Hyperplane.computed 6
  · exact Hyperplane.computed 7
  · exact Hyperplane.computed 8
  · exact Hyperplane.computed 9
  · exact Hyperplane.computed 10
  · exact Hyperplane.computed 11
  · exact Hyperplane.computed 12
  · exact Hyperplane.computed 13
  · exact Hyperplane.computed 14
  · exact Point.computed 0
  · exact Point.computed 1
  · exact Point.computed 2
  · exact Point.computed 3
  · exact Point.computed 4
  · exact Point.computed 5
  · exact Point.computed 6
  · exact Point.computed 7
  · exact Point.computed 8
  · exact Point.computed 9
  · exact Point.computed 10
  · exact Point.computed 11

/-- Every original descendant value follows from the accepted canonical table. -/
theorem accepted (i : Fin 48) : planeQueryValue? (requests i) = some (values i) := by
  rw [← planeQueryValueWith?_eq 1 GenusTwoPlaneLine.values GenusTwoPlaneLine.accepted
    (requests i) (by revert i; decide +kernel)]
  exact computed i

end AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay
