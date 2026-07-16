/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW

/-!
# API regression tests

These examples check that the public import and local-instance interfaces work
as intended. They are deliberately kept outside the production library.
-/

namespace AxiomaticGWTest

open AxiomaticGW TensorProduct

namespace CommFrobeniusAlgebra

/-- The canonical coalgebra can be installed locally without choosing a global
Frobenius structure. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (a : A) :
    letI : Coalgebra R A := F.toCoalgebra
    Coalgebra.counit (R := R) (A := A) a = F.counit a := by
  rfl

/-- The cocommutativity proof is compatible with the locally installed coalgebra. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (a : A) :
    TensorProduct.comm R A A (F.comul a) = F.comul a := by
  letI : Coalgebra R A := F.toCoalgebra
  letI : Coalgebra.IsCocomm R A := F.toIsCocomm
  exact Coalgebra.comm_comul R a

/-- The rank-two example remains available through the project entry point. -/
example (R : Type*) [CommRing R] :
    (AxiomaticGW.CommFrobeniusAlgebra.productAlgebra R).handleElement = 1 := by
  simp

end CommFrobeniusAlgebra

end AxiomaticGWTest
