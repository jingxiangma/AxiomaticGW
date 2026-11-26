/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Queries
public import AxiomaticGW.Linear.Contraction

/-!
# Explicit inverse-metric contractions for the fixed surfaces

The canonical copairing is `1 ⊗ pt + pt ⊗ 1 + H ⊗ H - ∑ Eᵢ ⊗ Eᵢ`.
In particular, every exceptional node contributes a minus sign. The formulas
below derive finite scalar contractions from the existing perfect pairing;
they do not assume a new metric or a numerical GW recurrence.
-/

@[expose] public section

namespace AxiomaticGW

open TensorProduct

namespace SurfaceCohomology

/-- The inverse of the surface trace pairing, with ordered node branches. -/
theorem copairing_eq (r : ℕ) :
    (frobenius r).pairing.copairing =
      (1 ⊗ₜ[ℚ] point r) + (point r ⊗ₜ[ℚ] 1) +
        (hyperplane r ⊗ₜ[ℚ] hyperplane r) -
          ∑ i : Fin r, exceptional r i ⊗ₜ[ℚ] exceptional r i := by
  apply (frobenius r).pairing.tensorEndEquiv.injective
  ext x
  simp only [SymmetricPerfectPairing.tensorEndEquiv_copairing, LinearMap.id_apply,
    map_add, map_sub, map_sum, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.sum_apply, SymmetricPerfectPairing.tensorEndEquiv_tmul,
    CommFrobeniusAlgebra.pairing_apply]
  change x = tracePairing (counit r) 1 x • point r +
    tracePairing (counit r) (point r) x • 1 +
    tracePairing (counit r) (hyperplane r) x • hyperplane r -
    ∑ i, tracePairing (counit r) (exceptional r i) x • exceptional r i
  have hsymm (y : SurfaceCohomology r) :
      tracePairing (counit r) y x = tracePairing (counit r) x y := by
    simp only [tracePairing_apply, mul_comm]
  simp only [hsymm, tracePairing_counit_one, tracePairing_counit_point,
    tracePairing_counit_hyperplane, tracePairing_counit_exceptional]
  apply (coordinates r).injective
  simp only [map_add, map_sub, map_smul, map_sum]
  change ((x.1, x.2.1, x.2.2) : ℚ × (ℚ × (Fin r → ℚ)) × ℚ) =
    x.2.2 • (0, 0, 1) + x.1 • (1, 0, 0) +
    x.2.1.1 • (0, (1, 0), 0) - ∑ i, (-x.2.1.2 i) • (0, (0, Pi.single i 1), 0)
  refine Prod.ext ?_ (Prod.ext (Prod.ext ?_ (funext fun i ↦ ?_)) ?_) <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, Prod.fst_sum, Prod.snd_sum, Prod.fst_zero,
    Prod.snd_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
    Finset.sum_apply, smul_eq_mul, mul_zero, mul_one, Pi.single_apply,
    mul_ite, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const_zero, zero_add, add_zero, sub_zero, zero_sub, neg_neg]

end SurfaceCohomology

namespace SurfaceBasisLabel

/-- Identify the query labels with the already constructed cohomology basis. -/
def indexEquiv (X : SurfaceTarget) :
    SurfaceBasisLabel X ≃ Unit ⊕ (Unit ⊕ Fin X.blowups) ⊕ Unit where
  toFun
    | .unit => .inl ()
    | .hyperplane => .inr (.inl (.inl ()))
    | .exceptional i => .inr (.inl (.inr i))
    | .point => .inr (.inr ())
  invFun
    | .inl _ => .unit
    | .inr (.inl (.inl _)) => .hyperplane
    | .inr (.inl (.inr i)) => .exceptional i
    | .inr (.inr _) => .point
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨⟩ | ((⟨⟩ | i) | ⟨⟩) <;> rfl

/-- A sum over query labels keeps all exceptional states as separate summands. -/
theorem sum_labels {X : SurfaceTarget} {A : Type*} [AddCommMonoid A]
    (f : SurfaceBasisLabel X → A) :
    (∑ a, f a) = f .unit + (f .hyperplane + ∑ i, f (.exceptional i)) + f .point := by
  rw [← (indexEquiv X).symm.sum_comp f]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, indexEquiv]
  exact (add_assoc _ _ _).symm

/-- The other basis label at an inverse-metric edge. -/
def dual {X : SurfaceTarget} : SurfaceBasisLabel X → SurfaceBasisLabel X
  | .unit => .point
  | .point => .unit
  | .hyperplane => .hyperplane
  | .exceptional i => .exceptional i

/-- Exceptional basis vectors have inverse pairing coefficient minus one. -/
def inverseWeight {X : SurfaceTarget} : SurfaceBasisLabel X → ℚ
  | .exceptional _ => -1
  | _ => 1

theorem dual_dual {X : SurfaceTarget} (a : SurfaceBasisLabel X) : a.dual.dual = a := by
  cases a <;> rfl

theorem inverseWeight_dual {X : SurfaceTarget} (a : SurfaceBasisLabel X) :
    a.dual.inverseWeight = a.inverseWeight := by
  cases a <;> rfl

/-- The labelled finite sum is the canonical inverse metric, not an extra input. -/
theorem copairing_eq_sum (X : SurfaceTarget) :
    (SurfaceCohomology.frobenius X.blowups).pairing.copairing =
      ∑ a : SurfaceBasisLabel X, a.inverseWeight • (a.value ⊗ₜ[ℚ] a.dual.value) := by
  rw [SurfaceCohomology.copairing_eq, sum_labels]
  simp only [inverseWeight, dual, value, one_smul, neg_smul, Finset.sum_neg_distrib]
  abel

end SurfaceBasisLabel

namespace SurfaceCohomology

/-- Finite evaluation of the existing ordered two-slot contraction. -/
theorem contractTwo_eq_sum (X : SurfaceTarget)
    (f : MultilinearMap ℚ (fun _ : Fin 2 ↦ SurfaceCohomology X.blowups) ℚ) :
    (frobenius X.blowups).pairing.contractTwo f =
      ∑ a : SurfaceBasisLabel X, a.inverseWeight *
        f (Fin.cons a.value (fun _ ↦ a.dual.value)) := by
  rw [SymmetricPerfectPairing.contractTwo_apply, SurfaceBasisLabel.copairing_eq_sum]
  simp only [map_sum, map_smul, TensorProduct.lift.tmul,
    SymmetricPerfectPairing.finTwoToBilin_apply, smul_eq_mul]

/-- Every separating node is a finite signed sum over the fixed surface basis. -/
theorem pairContract_eq_sum (X : SurfaceTarget) {S T : Type*}
    (f : MultilinearMap ℚ (fun _ : Option S ↦ SurfaceCohomology X.blowups) ℚ)
    (g : MultilinearMap ℚ (fun _ : Option T ↦ SurfaceCohomology X.blowups) ℚ)
    (a : S ⊕ T → SurfaceCohomology X.blowups) :
    (frobenius X.blowups).pairing.pairContract f g a =
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (f (Option.elim · b.value (a ∘ Sum.inl)) *
          g (Option.elim · b.dual.value (a ∘ Sum.inr))) := by
  rw [SymmetricPerfectPairing.pairContract_apply, contractTwo_eq_sum]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  simp only [MultilinearMap.currySum_apply', MultilinearMap.domDomCongr_apply,
    LinearMap.compMultilinearMap_apply, MultilinearMap.domCoprod_apply,
    LinearMap.mul'_apply]
  congr 1 <;> congr 1 <;> funext s <;> cases s <;> rfl

/-- The same ordered finite sum applies to a nonseparating node. -/
theorem selfContract_eq_sum (X : SurfaceTarget) {S : Type*}
    (f : MultilinearMap ℚ (fun _ : S ⊕ Fin 2 ↦ SurfaceCohomology X.blowups) ℚ)
    (a : S → SurfaceCohomology X.blowups) :
    (frobenius X.blowups).pairing.selfContract f a =
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        f (Sum.elim a (Fin.cons b.value (fun _ ↦ b.dual.value))) := by
  rw [SymmetricPerfectPairing.selfContract_apply, contractTwo_eq_sum]
  rfl

end SurfaceCohomology

end AxiomaticGW
