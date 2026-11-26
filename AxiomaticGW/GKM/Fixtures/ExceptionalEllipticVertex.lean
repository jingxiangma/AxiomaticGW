/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.EllipticLocalizationVertex
public import AxiomaticGW.GKM.Fixtures.ExceptionalGenusTwoCubic
import all Mathlib.Data.List.Sort

/-! # The two elliptic endpoints of a primitive exceptional fixed graph

The marked endpoint carrying a cubic cotangent insertion has excess degree.
At the other endpoint the flag cotangent and tangent-line Hodge terms cancel,
leaving the transverse Hodge term. These are the two elliptic source factors
in the producer's six genus-two cubic-descendant loci on a primitive axis.
-/

@[expose] public section
namespace AxiomaticGW.GKM.ExceptionalEllipticVertex
open EllipticHodge

variable {L : Type*} [Field L] [CharZero L]

/-- The cotangent term and the two tangent-line Hodge terms for any covering weight. -/
theorem unmarked_one_flag (u v w : L) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    source [] u v (fun _ : Fin 1 ↦ w) nativeMoment =
      1 / (24 * w^2) - (1 / u + 1 / v) / (24 * w) := by
  have f00 : flagProfiles 1 [] 0 0 = {fun _ ↦ 1} := by decide +kernel
  have f01 : flagProfiles 1 [] 0 1 = {fun _ ↦ 0} := by decide +kernel
  have f10 : flagProfiles 1 [] 1 0 = {fun _ ↦ 0} := by decide +kernel
  have f11 : flagProfiles 1 [] 1 1 = ∅ := by decide +kernel
  have v00 : nativeMoment 0 0 (Sum.elim ([] : List ℕ).get (fun _ : Fin 1 ↦ 1)) = 1 / 24 := by
    decide +kernel
  have v10 : nativeMoment 1 0 (Sum.elim ([] : List ℕ).get (fun _ : Fin 1 ↦ 0)) = 1 / 24 := by
    decide +kernel
  have v01 : nativeMoment 0 1 (Sum.elim ([] : List ℕ).get (fun _ : Fin 1 ↦ 0)) = 1 / 24 := by
    decide +kernel
  simp only [source, Fin.sum_univ_two, f00, f01, f10, f11, Finset.sum_singleton, Finset.sum_empty,
    Fin.prod_univ_one, v00, v01, v10]
  norm_num
  field_simp
  ring

/-- At an unramified flag the tangent-line term cancels the cotangent term. -/
theorem unmarked (w t : L) (hw : w ≠ 0) (ht : t ≠ 0) :
    source [] w t (fun _ : Fin 1 ↦ w) nativeMoment = -1 / (24 * w * t) := by
  rw [unmarked_one_flag w t w hw ht hw]
  field_simp
  ring

/-- Both ordered distributions of the marking in the elliptic split have zero contribution. -/
theorem cubic_split (m : Fin 2) (w t w' t' : EquivariantCoefficients.Coefficient) :
    ExceptionalGenusTwoCubic.contribution 1 m =
      source [3] w t (fun _ : Fin 1 ↦ w) nativeMoment *
        source [] w' t' (fun _ : Fin 1 ↦ w') nativeMoment := by
  rw [source_zero_of_excess [3] w t _ _ (by decide : 1 + 1 < 3), zero_mul]
  rfl

end AxiomaticGW.GKM.ExceptionalEllipticVertex
