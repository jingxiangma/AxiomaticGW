/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.AncestorPolynomial

/-! # Singleton ancestor keys for genus-two reconstruction -/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
variable {X : SurfaceTarget}

/-- The genus-two ancestor key at a specified full class, basis state and cotangent power. -/
def oneMarkingKey (beta : X.Curve) (a : SurfaceBasisLabel X) (power : ℕ) : SurfaceAncestorKey X :=
  ⟨2, beta, {⟨a, power⟩}, by simp only [Multiset.card_singleton]; decide⟩

/-- Replacing a numbered singleton by its unique insertion preserves the ancestor query. -/
theorem ofLabels_oneMarkingKey (beta : X.Curve) (e : Fin 1 → ℕ) (a : Fin 1 → SurfaceBasisLabel X)
    (h : StableArity 2 (Fin 1)) :
    SurfaceAncestorKey.ofLabels 2 (Fin 1) h beta e a = oneMarkingKey beta (a 0) (e 0) := by
  apply (SurfaceAncestorKey.eq_iff _ _).mpr
  refine ⟨rfl, rfl, ?_⟩
  change (Finset.univ : Finset (Fin 1)).val.map _ = _
  rw [show (Finset.univ : Finset (Fin 1)) = {0} by decide]
  rfl

end AxiomaticGW.SurfaceGenusTwo
