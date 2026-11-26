/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoL24ConstantGuard

/-! # Consumers for the full L24 constant guard -/

@[expose] public section

namespace AxiomaticGWTest.GenusTwoL24ConstantGuard
open AxiomaticGW

set_option maxRecDepth 20000

/-- An actual H graph is skipped with three added points at an F1 source
H+2E1, whose signed exceptional multiplicity is -2. -/
theorem signed_shifted_f1_term_zero :
    SurfaceGenusTwo.guardedConstantPointContraction .hirzebruchOne (L24Gluing.term 57)
      ![3, 1] 3
      ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 0 := by
  apply SurfaceGenusTwo.guardedConstantPointContraction_eq_zero
  decide +kernel

/-- The unshifted class is beta=H+E1+2E2, with alpha1=-1 and alpha2=-2.
The tested full constant has source beta+E1=H+2E1+2E2, hence source
alpha1=-2 and alpha2=-2, and five added points. -/
theorem signed_shifted_bl2_full_constant :
    L24Relation.pointConstantGuarded .blowupTwo 5
      ![3, 3, 1]
      ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] =
    L24Relation.pointConstant .blowupTwo 5
      ![3, 3, 1]
      ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] :=
  L24Relation.pointConstantGuarded_eq _ _ _ _

/-- Class zero and no added points require no exceptional positive-energy premise. -/
theorem zero_class_full_constant (X : SurfaceTarget)
    (a : Fin 4 → SurfaceBasisLabel X) :
    L24Relation.pointConstantGuarded X 0 0 a = L24Relation.pointConstant X 0 0 a :=
  L24Relation.pointConstantGuarded_eq _ _ _ _

/-- A rational fundamental graph at the class-zero boundary is retained by
the early guard; its scalar value is not replaced with an assumed zero. -/
theorem rational_boundary_retained :
    let z : GluingExpression.CotangentTerm 0 (Fin 3) :=
      GluingExpression.CotangentTerm.fundamental 0 (Fin 3)
        (by norm_num [StableArity]) 0
    SurfaceGenusTwo.guardedConstantPointContraction .blowupTwo z 0 0
      ![.unit, .unit, .point] =
      z.expression.scalarPointContraction .blowupTwo
        (SurfacePointPullback.vertex .blowupTwo (SurfaceGenusTwo.constantVertex .blowupTwo))
        z.decoration z.labels 0 0 ![.unit, .unit, .point] := by
  dsimp only
  apply SurfaceGenusTwo.guardedConstantPointContraction_of_lt
  decide +kernel

end AxiomaticGWTest.GenusTwoL24ConstantGuard
