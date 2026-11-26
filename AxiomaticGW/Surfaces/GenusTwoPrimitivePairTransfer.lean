/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.MixedAncestorReduction

/-! # Mixed transfer of two first powers in anticanonical degree one

The main component keeps both cotangent powers or absorbs one calibration at
either named marking. A positive tail exhausts the full effective class.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open SurfaceDescendant
variable {X : SurfaceTarget}

/-- Retain the two occurrences, including repetitions, in the symmetric ancestor variable. -/
def pairKey (beta : X.Curve) (a b : SurfaceInsertion X) : SurfaceAncestorKey X :=
  ⟨2, beta, {a, b}, by omega⟩

private theorem ofLabels_pairKey (beta : X.Curve) (e : Fin 2 → ℕ)
    (a : Fin 2 → SurfaceBasisLabel X) (h : StableArity 2 (Fin 2)) :
    SurfaceAncestorKey.ofLabels 2 (Fin 2) h beta e a =
      pairKey beta ⟨a 0, e 0⟩ ⟨a 1, e 1⟩ := by
  apply (SurfaceAncestorKey.eq_iff _ _).mpr
  refine ⟨rfl, rfl, ?_⟩
  change (Finset.univ : Finset (Fin 2)).val.map _ = _
  rw [show (Finset.univ : Finset (Fin 2)) = {0,1} by decide]
  rfl

private theorem primitive_tail (beta : X.Curve) (he : X.effective.energy beta = 1) :
    X.positiveTailSplittings beta = {(0, beta)} := by
  rw [X.positiveTailSplittings_eq]
  ext ⟨b, c⟩
  rw [X.effective.mem_positiveTailSplittings, Finset.mem_singleton]
  constructor
  · rintro ⟨h, hc⟩
    have hc' := (X.effective.energy_eq_zero_iff c).not.mpr hc
    have he' := congrArg X.effective.energy h
    rw [map_add, he] at he'
    have hb := (X.effective.energy_eq_zero_iff b).mp (by omega)
    simpa only [hb, zero_add] using congrArg (Prod.mk (0 : X.Curve)) h
  · rintro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨zero_add _, ?_⟩
    intro hz
    rw [hz, map_zero] at he
    omega

private theorem zero_tail : X.positiveTailSplittings 0 = ∅ := by
  rw [SurfaceTarget.positiveTailSplittings, X.splittings_eq, X.effective.splittings_zero]
  rw [Finset.filter_singleton, if_neg (not_not_intro rfl)]

/-- All calibrated main-component insertions after one positive tail. The
retained first power stays at the opposite marking in each of the two sums. -/
def firstPairTails (beta : X.Curve) (a b : SurfaceBasisLabel X) :
    RationalTerms (SurfaceAncestorKey X) :=
  (∑ c : SurfaceBasisLabel X, RationalTerms.scale (reconstructedCalibrationMatrix X 1 beta c b)
    (RationalTerms.term 1 {pairKey 0 ⟨a, 1⟩ ⟨c, 0⟩})) +
  ∑ c : SurfaceBasisLabel X, RationalTerms.scale (reconstructedCalibrationMatrix X 1 beta c a)
    (RationalTerms.term 1 {pairKey 0 ⟨c, 0⟩ ⟨b, 1⟩})

/-- The complete two-marked mixed expansion at energy one. -/
theorem mixed_firstPair_primitive (beta : X.Curve) (he : X.effective.energy beta = 1)
    (a : Fin 2 → SurfaceBasisLabel X) (h : StableArity 2 (Fin 2)) :
    mixedAncestorTerms 2 (Fin 2) h (List.finRange 2) beta (fun _ ↦ 1) 0 a =
      RationalTerms.term 1 {pairKey beta ⟨a 0, 1⟩ ⟨a 1, 1⟩} +
        firstPairTails beta (a 0) (a 1) := by
  have hl : List.finRange 2 = [0, 1] := rfl
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rw [hl]
  simp only [mixedAncestorTerms, transferMark, Function.update_self,
    Function.update_of_ne h01, Function.update_of_ne h01.symm,
    Pi.zero_apply, Nat.zero_add, primitive_tail beta he, zero_tail, Finset.sum_empty,
    Finset.sum_singleton, ofLabels_pairKey, add_zero, firstPairTails, add_assoc]

end AxiomaticGW.SurfaceGenusTwo
