/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalBoundaryData
public import AxiomaticGW.GKM.Fixtures.PlaneLineBoundarySplitting
public import Mathlib.Tactic.FieldSimp

/-!
# Stabilized primitive exceptional classes on the two blowups

Three insertions are lifts of the own exceptional divisor. The fourth is an
adjacent toric divisor. Its ordinary coordinates distinguish the two exceptional
curves of the two-point blowup. The stabilized bridge has weight minus one;
the unit and separating identifications use the same labelled graph family as
the plane and the actual exceptional entry of the surface copairing.
-/

@[expose] public section
namespace AxiomaticGW.GKM.ExceptionalBoundaryClass
open ExceptionalBoundaryData EquivariantCoefficients TensorProduct
noncomputable section

/-- Fixed surface target of each incoming curve. -/
def target : Case → SurfaceTarget | .f1 => .hirzebruchOne | .first | .second => .blowupTwo

/-- The exceptional class retains its actual generator on the two-point blowup. -/
def own : (c : Case) → Fin (target c).blowups
  | .f1 | .first => ⟨0, by decide⟩
  | .second => ⟨1, by decide⟩

def beta (c : Case) := (target c).exceptionalCurve (own c)

/-- Uniform source serialization of surface states. -/
def slot {X : SurfaceTarget} : SurfaceBasisLabel X → Fin 5
  | .unit => 0 | .hyperplane => 1 | .exceptional i => if i.val = 0 then 2 else 3 | .point => 4

/-- The adjacent toric divisors are H-E, H-E₁-E₂ and H-E₂ in the three cases. -/
def fourth : Case → Fin 5 → ℚ
  | .f1 => ![0, 1, -1, 0, 0]
  | .first => ![0, 1, -1, -1, 0]
  | .second => ![0, 1, 0, -1, 0]

/-- Ordinary specialization identifies every entry of all four actual insertion lifts. -/
theorem insertion_coordinates (c : Case) (j : Fin 4) (s : Fin 5) :
    atZero (lifts c j s) = if j = 3 then fourth c s else
      if s = slot (SurfaceBasisLabel.exceptional (X := target c) (own c)) then 1 else 0 := by
  cases c <;> fin_cases j <;> fin_cases s <;>
    norm_num [lifts, fourth, slot, own, atZero, MvPolynomial.eval₂Hom_X'] <;> decide +kernel

/-- All three sets of source markings give the same labelled raw bridge and unit placements. -/
theorem marking_bindings (c : Case) : baseLeg c = PlaneLineBoundaryData.baseLeg ∧
    leftLeg c = PlaneLineBoundaryData.leftLeg ∧ rightLeg c = PlaneLineBoundaryData.rightLeg := by
  cases c <;> exact ⟨rfl, rfl, rfl⟩

/-- The four-point contribution before integrating the two contracted endpoints. -/
def weight (c : Case) : Coefficient :=
  let f := factors c
  f.edge * f.tangent * f.insertions /
    (f.automorphisms * (f.eulerLeft * f.eulerRight) * (f.flagLeft * f.flagRight))

private theorem identities (c : Case) :
    let f := factors c
    f.edge = -1 / f.flagLeft ^ 2 ∧ f.tangent = f.eulerLeft * f.eulerRight ∧
    f.insertions = -(f.flagLeft ^ 4) ∧ f.flagRight = -f.flagLeft ∧ f.automorphisms = 1 := by
  cases c <;> dsimp only [factors] <;> refine ⟨?_, ?_, ?_, ?_, rfl⟩ <;> ring

private theorem nonvanishing (c : Case) :
    (factors c).flagLeft ≠ 0 ∧ (factors c).eulerLeft ≠ 0 ∧ (factors c).eulerRight ≠ 0 := by
  have hp : x*y - y^2 ≠ 0 := by
    rw [show x*y-y^2 = y*(x-y) by ring]
    exact mul_ne_zero y_ne_zero x_sub_y_ne_zero
  have hq : -x^2+x*y ≠ 0 := by
    rw [show -x^2+x*y = -x*(x-y) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr x_ne_zero) x_sub_y_ne_zero
  cases c
  · exact ⟨x_sub_y_ne_zero, hp, hq⟩
  · exact ⟨x_sub_y_ne_zero, hp, hq⟩
  · exact ⟨y_ne_zero, mul_ne_zero (neg_ne_zero.mpr x_ne_zero) y_ne_zero, hp⟩

theorem weight_eq (c : Case) : weight c = -1 := by
  obtain ⟨he, ht, hi, hf, ha⟩ := identities c
  obtain ⟨hw, hl, hr⟩ := nonvanishing c
  rw [weight, he, ht, hi, hf, ha]
  field_simp [hw, hl, hr]

/-- The native scalar claims agree with the expanded vertex and edge weights at both arities. -/
theorem incoming (c : Case) : (factors c).boundary = weight c ∧
    (factors c).psiLeft = weight c / (factors c).flagLeft ∧
    (factors c).psiRight = weight c / (factors c).flagRight := by
  rw [weight_eq]
  cases c <;> exact ⟨rfl, rfl, rfl⟩

theorem base_regular (c : Case) : Specializes (weight c) (-1) := by
  simpa only [map_neg, map_one] using specializes_of_eq_polynomial (f := weight c) (-1)
    (by simpa only [map_neg, map_one] using weight_eq c)

/-- Project the entire five-point fixed-locus packet, including both cotangent poles. -/
def pairing (c : Case) (ev : StrataModule 0 (Fin 5) →ₗ[ℚ] ℚ) : Coefficient :=
  let f := factors c
  weight c * (ev PlaneLineBoundaryClass.unitClass : Coefficient) +
    f.psiLeft * (ev (StrataModule.basis (PlaneLineBoundaryClass.unitStratum 0 1)) : Coefficient) +
    f.psiRight * (ev (StrataModule.basis (PlaneLineBoundaryClass.unitStratum 1 1)) : Coefficient)

/-- Opposite flag poles cancel modulo the two attached original psi relations.
All three classes specialize to minus the same sum of raw boundary placements. -/
theorem unit_regular (c : Case) (ev : StrataModule 0 (Fin 5) →ₗ[ℚ] ℚ)
    (h : ∀ i, ev ((PlaneLineBoundaryClass.attach i).map (RelationCertificate.interpret
      (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1))) = 0) :
    Specializes (pairing c ev) (ev (-PlaneLineBoundaryClass.unitClass)) := by
  have he (i : Fin 2) :
      ev (StrataModule.basis (PlaneLineBoundaryClass.unitStratum i 1)) =
        ev (StrataModule.basis PlaneLineBoundaryClass.central) := by
    have hi := h i
    rwa [PlaneLineBoundaryClass.attached_relation, map_sub, sub_eq_zero] at hi
  have hu : pairing c ev = (ev (-PlaneLineBoundaryClass.unitClass) : Coefficient) := by
    rw [pairing, (incoming c).2.1, (incoming c).2.2, (identities c).2.2.2.1, div_neg,
      weight_eq, he 0, he 1, map_neg, Rat.cast_neg]
    ring
  simpa only [atZero, MvPolynomial.eval₂Hom_C, RingHom.id_apply] using
    specializes_of_eq_polynomial (f := pairing c ev)
      (MvPolynomial.C (ev (-PlaneLineBoundaryClass.unitClass))) (by rw [embed_C, hu])

/-- The ordinary integral from the surface primary reconstruction checks the signed class
against the divisor class in the fourth slot, with the full exceptional curve held fixed. -/
theorem integral_comparison (c : Case) :
    (∑ a : SurfaceBasisLabel (target c), fourth c (slot a) *
      SurfaceGenusZero.primaryValue (target c) (beta c)
        {.exceptional (own c), .exceptional (own c), .exceptional (own c), a}) = -1 := by
  cases c <;> decide +kernel

end
end AxiomaticGW.GKM.ExceptionalBoundaryClass
