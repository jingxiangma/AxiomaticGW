/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Linear.PairingTransport
public import Mathlib.Data.Fin.VecNotation

/-!
# Raising the node index of a two-point correlator

The first input is the attaching node; the second is the retained marking.
Perfectness raises the first index without choosing a basis. The resulting
operator is characterized by pairing with every node state. Its contraction
and transport formulas connect actual two-point invariants to rational-tail
operators and to a change of state-space coordinates.
-/

@[expose] public section

namespace AxiomaticGW.SymmetricPerfectPairing
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Raise the first, node index, leaving the second input as the operator argument. -/
noncomputable def raiseTwoPoint (P : SymmetricPerfectPairing R V)
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) : Module.End R V :=
  P.toDual.symm.toLinearMap.comp (finTwoToBilin f).flip

/-- Pairing with a node state recovers the original ordered correlator. -/
theorem raiseTwoPoint_pairing (P : SymmetricPerfectPairing R V)
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) (x y : V) :
    P.form x (P.raiseTwoPoint f y) = f ![x, y] := by
  rw [P.isSymm.eq, ← P.toDual_apply]
  change P.toDual (P.toDual.symm ((finTwoToBilin f).flip y)) x = _
  rw [LinearEquiv.apply_symm_apply]
  change finTwoToBilin f x y = _
  rw [finTwoToBilin_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The paired two-point values uniquely determine the operator. -/
theorem raiseTwoPoint_unique (P : SymmetricPerfectPairing R V)
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) (T : Module.End R V)
    (h : ∀ x y, P.form x (T y) = f ![x, y]) : T = P.raiseTwoPoint f := by
  ext y
  apply P.toDual.injective
  ext x
  rw [P.toDual_apply, P.toDual_apply, P.isSymm.eq (T y) x,
    P.isSymm.eq (P.raiseTwoPoint f y) x, h, P.raiseTwoPoint_pairing]

/-- A zero correlator raises to the zero operator. -/
theorem raiseTwoPoint_zero (P : SymmetricPerfectPairing R V) :
    P.raiseTwoPoint (0 : MultilinearMap R (fun _ : Fin 2 ↦ V) R) = 0 := by
  symm
  apply P.raiseTwoPoint_unique
  intro x y
  simp only [LinearMap.zero_apply, map_zero, zero_apply]

variable [Module.Free R V] [Module.Finite R V]

/-- Sewing a linear main contribution to the two-point tail inserts the raised state. -/
theorem raiseTwoPoint_contract (P : SymmetricPerfectPairing R V)
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) (ell : Module.Dual R V) (y : V) :
    TensorProduct.lift
        (((LinearMap.mul R R).comp ell).compl₂ ((finTwoToBilin f).flip y))
        P.copairing = ell (P.raiseTwoPoint f y) := by
  let x := P.toDual.symm ell
  have hx : P.toDual x = ell := P.toDual.apply_symm_apply ell
  have hy : (finTwoToBilin f).flip y = P.toDual (P.raiseTwoPoint f y) := by
    change _ = P.toDual (P.toDual.symm _)
    exact (P.toDual.apply_symm_apply _).symm
  rw [← hx, hy, P.contract_toDual_mul_toDual, ← P.toDual_apply, hx]

variable {W : Type*} [AddCommGroup W] [Module R W]

omit [Module.Free R V] [Module.Finite R V] in
/-- The raised operator transports by conjugation with the state-space equivalence. -/
theorem raiseTwoPoint_comap (P : SymmetricPerfectPairing R V) (e : W ≃ₗ[R] V)
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) (y : W) :
    e ((P.comap e).raiseTwoPoint (f.compLinearMap (fun _ ↦ e.toLinearMap)) y) =
      P.raiseTwoPoint f (e y) := by
  apply P.toDual.injective
  ext x
  obtain ⟨z, rfl⟩ := e.surjective x
  rw [P.toDual_apply, P.toDual_apply, P.isSymm.eq _ (e z), P.isSymm.eq _ (e z),
    ← P.comap_apply e, raiseTwoPoint_pairing, P.raiseTwoPoint_pairing,
    MultilinearMap.compLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

end AxiomaticGW.SymmetricPerfectPairing
