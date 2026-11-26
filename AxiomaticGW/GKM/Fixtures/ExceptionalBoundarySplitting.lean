/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalBoundaryClass

/-! # Exceptional node pairing on the rational-tail section -/

@[expose] public section
namespace AxiomaticGW.GKM.ExceptionalBoundaryClass
open ExceptionalBoundaryData EquivariantCoefficients TensorProduct
noncomputable section

/-- Reconstruct the primary tail with own exceptional, unit and each actual node state. -/
def tailValue (c : Case) (degree : (target c).Curve) (a : SurfaceBasisLabel (target c)) : ℚ :=
  SurfaceGenusZero.primaryValue (target c) degree {.exceptional (own c), .unit, a}

/-- The sole surviving tail has value minus one at its own node state; the
positive-degree tail vanishes even at the other equal-energy exceptional state. -/
theorem tail_support (c : Case) : ∀ a : SurfaceBasisLabel (target c),
    tailValue c 0 a = (if a = .exceptional (own c) then -1 else 0) ∧
    tailValue c (beta c) a = 0 := by cases c <;> decide +kernel

/-- Native ordinary tail coefficients and original reconstruction agree for every state. -/
theorem tail_replay (c : Case) (a : SurfaceBasisLabel (target c)) :
    atZero (tail c 0 (slot a)) = tailValue c 0 a ∧
    atZero (tail c 1 (slot a)) = tailValue c (beta c) a := by
  have h (c : Case) (s : Fin 5) :
      atZero (tail c 0 s) = (if s = slot (SurfaceBasisLabel.exceptional
        (X := target c) (own c)) then -1 else 0) ∧ atZero (tail c 1 s) = 0 := by
    cases c <;> fin_cases s <;> constructor <;>
      norm_num [tail, slot, own, atZero, MvPolynomial.eval₂Hom_X'] <;> decide +kernel
  have labels (c : Case) : ∀ a : SurfaceBasisLabel (target c),
      slot a = slot (SurfaceBasisLabel.exceptional (X := target c) (own c)) ↔
        a = .exceptional (own c) := by cases c <;> decide +kernel
  constructor
  · rw [(h c _).1, (tail_support c a).1]
    by_cases ha : a = .exceptional (own c)
    · rw [if_pos ha, if_pos ((labels c a).mpr ha)]
    · rw [if_neg ha, if_neg (ha ∘ (labels c a).mp)]
  · exact (h c _).2.trans (tail_support c a).2.symm

/-- The minus sign from the exceptional inverse pairing cancels the tail's self-intersection.
The full ordered degree-split contraction retains the main own-exceptional class. -/
theorem tail_contraction (c : Case) {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : (target c).Curve → SurfaceBasisLabel (target c) → V) :
    (∑ b ∈ (target c).splittings (beta c), ∑ a : SurfaceBasisLabel (target c),
      (a.inverseWeight * tailValue c b.1 a) • v b.2 a.dual) =
      v (beta c) (.exceptional (own c)) := by
  have hsplit : (target c).splittings (beta c) = {(0, beta c), (beta c, 0)} := by
    cases c <;> decide +kernel
  have he : ((0, beta c) : (target c).Curve × (target c).Curve) ≠ (beta c, 0) := by
    cases c <;> decide +kernel
  rw [hsplit, Finset.sum_pair he]
  simp only [(tail_support c _).2, mul_zero, zero_smul, Finset.sum_const_zero, add_zero]
  apply (Finset.sum_eq_single (.exceptional (own c)) ?_ ?_).trans
  · rw [(tail_support c _).1, if_pos rfl]
    change ((-1 : ℚ) * -1) • v (beta c) (.exceptional (own c)) = _
    norm_num
  · intro a _ ha
    rw [(tail_support c _).1, if_neg ha, mul_zero, zero_smul]
  · intro impossible
    exact (impossible (Finset.mem_univ _)).elim

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- The signed exceptional five-marked packet is the pullback of the four-marked one. -/
theorem map_unit (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N) (hbase : (WDVV.expression 0).Compatible A F N)
    (hup : ∀ z ∈ (WDVV.expression 0).addMarkings 1, z.Compatible A F N) :
    (A 0 (Option (Fin 4))).map
        (StrataModule.relabel PlaneLineBoundaryClass.labels (-PlaneLineBoundaryClass.unitClass)) =
      C.forget 0 (Fin 4) WDVV.stableArity ((A 0 (Fin 4)).map (-PlaneLineBoundaryClass.baseClass))
      := by
  rw [map_neg, map_neg, PlaneLineBoundaryClass.map_unit A F N H hbase hup, map_neg, map_neg]

/-- Restrict the signed class to the actual marked 15|234 section. Its component
gluing formula includes every ordered class splitting and the negative exceptional metric. -/
theorem map_section (c : Case) (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N) (Htail : PsiBoundaryExpansion.TailForgetCompatible C)
    (hbase : (WDVV.expression 0).Compatible A F N)
    (hup : ∀ z ∈ (WDVV.expression 0).addMarkings 1, z.Compatible A F N)
    (v : (target c).Curve → SurfaceBasisLabel (target c) → C.H 0 (Fin 4))
    (hmain : v (beta c) (.exceptional (own c)) =
      (A 0 (Fin 4)).map (-PlaneLineBoundaryClass.baseClass)) :
    PsiBoundaryExpansion.tailRestriction C WDVV.stableArity 0
        ((A 0 (Option (Fin 4))).map
          (StrataModule.relabel PlaneLineBoundaryClass.labels
            (-PlaneLineBoundaryClass.unitClass))) =
      C.rename 0 (Fin 4) (Option {t : Fin 4 // t ≠ 0}) WDVV.stableArity
        (PsiBoundaryExpansion.tailMainStable WDVV.stableArity 0) (Equiv.optionSubtypeNe 0).symm
        (∑ b ∈ (target c).splittings (beta c), ∑ a : SurfaceBasisLabel (target c),
          (a.inverseWeight * tailValue c b.1 a) • v b.2 a.dual) ⊗ₜ[R] 1 := by
  rw [tail_contraction, hmain, map_unit A F N H hbase hup]
  exact Htail 0 (Fin 4) WDVV.stableArity 0 _

end
end AxiomaticGW.GKM.ExceptionalBoundaryClass
