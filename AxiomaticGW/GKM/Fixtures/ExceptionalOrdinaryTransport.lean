/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalMarkedTransport
public import AxiomaticGW.GKM.RegularSpecialization

/-!
# Ordinary specialization of marked exceptional graph sums

The pinned hyperplane lift on the first exceptional curve of Bl₂ contributes
an extra character times the unit. Expand the product over the marked legs
and sum the fixed loci before specializing. Regularity is needed only for
the total coefficients with chosen hyperplane markings replaced by units.
-/

@[expose] public section
namespace AxiomaticGW.GKM.ExceptionalOrdinaryTransport
open EquivariantCoefficients ExceptionalMarkedTransport ExceptionalMarkedGraphSupport
open ExceptionalCharacterField
open CurveReplay.OneBlowup renaming tables → f1
open SurfaceFrames.OneBlowup renaming request → oneFrame
open SurfaceFrames.TwoBlowups renaming request → twoFrame
noncomputable section

/-- The unshifted marking on F₁. The other exceptional divisor restricts to zero. -/
def base (i : Fin 2) (r : SurfaceBasisLabel .hirzebruchOne → Coefficient) :
    SurfaceBasisLabel .blowupTwo → Coefficient
  | .unit => r .unit
  | .point => r .point
  | .hyperplane => r .hyperplane
  | .exceptional j => if i = j then r (.exceptional 0) else 0

/-- Replacing a hyperplane marking by the unit contributes a character on the first axis. -/
def shift (i : Fin 2) : Coefficient := if i = 0 then x else 0

private theorem shift_zero (i : Fin 2) : Specializes (shift i) 0 := by
  fin_cases i
  · change Specializes x 0
    simpa only [atZero, MvPolynomial.eval₂Hom_X', Pi.zero_apply] using
      specializes_of_eq_polynomial (MvPolynomial.X 0) (f := x) rfl
  · change EquivariantCoefficients.Specializes 0 0
    simpa only [map_zero] using specializes_of_eq_polynomial 0 rfl

variable {ι : Type*} [Fintype ι] (i : Fin 2) (d : ℕ+) (a : List (SurfaceInsertion .blowupTwo))
  (g : ι → MarkedAt f1 ((d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0) a.length)

/-- The F₁ restriction at the actual fixed vertex selected by a marking. -/
abbrev restriction (j : ι) (k : Fin a.length) (b : SurfaceBasisLabel .hirzebruchOne) :=
  oneFrame.restrictions ((g j).1.2.2.val.image ((g j).2 k)) (stateIndex b)

/-- The unit restriction if the marked insertion is a hyperplane, and zero otherwise. -/
abbrev unitAt (j : ι) (k : Fin a.length) :=
  if (a.get k).label = .hyperplane then restriction d a g j k .unit else 0

/-- Sum over all loci with the marked subset replaced by unit restrictions at its hyperplanes.
Any chosen non-hyperplane marking contributes zero. Cotangent powers stay in the graph weights. -/
def replacementSum (w : ι → Coefficient) (s : Finset (Fin a.length)) : Coefficient :=
  ∑ j, ((∏ k ∈ s, unitAt d a g j k) *
    ∏ k ∈ sᶜ, base i (restriction d a g j k) (a.get k).label) * w j

/-- The exact equivariant decomposition groups equal powers of the hyperplane-lift character. -/
theorem expansion (w : ι → Coefficient) :
    ∑ j, sourceProduct i d a (g j) * w j =
      ∑ s : Finset (Fin a.length), (shift i)^s.card * replacementSum i d a g w s := by
  have h (j : ι) (k : Fin a.length) : pullRestriction i (restriction d a g j k) (a.get k).label =
      shift i * unitAt d a g j k + base i (restriction d a g j k) (a.get k).label := by
    unfold unitAt
    generalize (a.get k).label = b
    cases b <;> simp [base, pullRestriction, shift, add_comm]
  have hp (j : ι) : sourceProduct i d a (g j) =
      ∑ s : Finset (Fin a.length), ((shift i)^s.card * ∏ k ∈ s, unitAt d a g j k) *
        ∏ k ∈ sᶜ, base i (restriction d a g j k) (a.get k).label := by
    change (∏ k, pullRestriction i (restriction d a g j k) (a.get k).label) = _
    simp_rw [h, Fintype.prod_add, Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hp, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [replacementSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- On either positive exceptional axis the transported marked graph sum has the unshifted
ordinary value, provided the sums over all loci for the replaced states are regular. -/
theorem ordinary (genus : ℕ) (w : ι → Coefficient) (v : Finset (Fin a.length) → ℚ)
    (hregular : ∀ s, Specializes (replacementSum i d a g w s) (v s)) :
    Specializes (∑ j, insertionFactor (targetQuery i d genus a) twoFrame.restrictions
      (markedEquiv i d a.length (g j)) * sector i (w j)) (v ∅) := by
  have hf : ∑ j, insertionFactor (targetQuery i d genus a) twoFrame.restrictions
      (markedEquiv i d a.length (g j)) * sector i (w j) =
      sector i (∑ j, sourceProduct i d a (g j) * w j) := by
    simp only [product_transport, map_sum, map_mul]
  rw [hf, expansion]
  suffices hs : Specializes (∑ s, (shift i)^s.card * replacementSum i d a g w s) (v ∅) by
    fin_cases i
    · exact hs
    · exact (specializes_iff _ _).mpr hs
  have h (s : Finset (Fin a.length)) : Specializes
      ((shift i)^s.card * replacementSum i d a g w s) (if s = ∅ then v ∅ else 0) := by
    have ht := ((shift_zero i).pow s.card).mul (hregular s)
    by_cases he : s = ∅
    · subst s
      simpa only [Finset.card_empty, pow_zero, one_mul, ↓reduceIte] using ht
    · have hc : s.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      simpa only [if_neg he, zero_pow hc, zero_mul] using ht
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using
    Specializes.sum Finset.univ _ _ (fun s _ ↦ h s)

end
end AxiomaticGW.GKM.ExceptionalOrdinaryTransport
