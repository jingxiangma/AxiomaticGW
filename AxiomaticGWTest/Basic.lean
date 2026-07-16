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

/-- The bundled correlator theory exposes the nonseparating gluing law. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (g : ℕ) :
    F.pairing.selfContract (F.correlator g (Fin 1 ⊕ Fin 2)) =
      F.correlator (g + 1) (Fin 1) := by
  exact (F.toTopologicalCorrelatorTheory.nonseparating g (Fin 1))

/-- The bundled correlator theory exposes the separating gluing law. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (g₁ g₂ : ℕ) :
    F.pairing.pairContract (F.correlator g₁ (Option (Fin 1)))
        (F.correlator g₂ (Option (Fin 1))) =
      F.correlator (g₁ + g₂) (Fin 1 ⊕ Fin 1) := by
  exact (F.toTopologicalCorrelatorTheory.separating g₁ g₂ (Fin 1) (Fin 1))

/-- The base-ring example computes every genus and finite arity. -/
example (R : Type*) [CommRing R] (g : ℕ) (a : Fin 3 → R) :
    (AxiomaticGW.CommFrobeniusAlgebra.baseRing R).correlator g (Fin 3) a =
      ∏ i, a i := by
  simp

/-- Restriction to stable arities preserves the underlying correlator. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) :
    F.toTopologicalCohFT.omega 0 (Fin 3) AxiomaticGW.StableArity.zero_fin_three =
      F.correlator 0 (Fin 3) := by
  rfl

/-- The three-point product extracted from the forward theory is the original
algebra multiplication. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (x y : A) :
    F.toTopologicalCorrelatorTheory.product x y = x * y := by
  exact F.toTopologicalCorrelatorTheory_product x y

end CommFrobeniusAlgebra

end AxiomaticGWTest
