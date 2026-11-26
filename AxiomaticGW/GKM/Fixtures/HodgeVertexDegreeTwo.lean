/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.GenusTwoVertexHodgeReduction
public import AxiomaticGW.GKM.Fixtures.HodgeDegreeTwoRawRelation
public import AxiomaticGW.CohFT.Tautological

/-! # Recovering the λ₁² sector from λ₂ for surface localization vertices

The two sectors have the same top-degree constraint. Each has a single reduced
signature, with one marking of cotangent power two. The accepted one-marked raw
strata relation gives their factor of two after any common realization and integration.
-/

public section
namespace AxiomaticGW.GKM.HodgeVertexDegreeTwo
open GenusTwoVertexHodgeReduction AdmcyclesHodgeStrataCandidates

/-- Seed equality at ψ² propagates to arbitrary ordered cotangent powers by the
string and dilaton equations for the two sectors. -/
theorem all_powers (U V : List ℕ → ℚ) (hu : Recurrences 1 1 U) (hv : Recurrences 0 2 V)
    (base : U [2] = 2 * V [2]) (p : List ℕ) : U p = 2 * V p := by
  have htwice : Recurrences 1 1 (fun q ↦ 2 * V q) := {
    degree q hd := by rw [hv.degree q (by omega), mul_zero]
    relabel h := congrArg (2 * ·) (hv.relabel h)
    string q := by
      rw [hv.string, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by split_ifs <;> first | rfl | exact mul_zero _
    dilaton q := by rw [hv.dilaton, mul_left_comm] }
  let seed (k : ↥seeds) := U k.val.2.2
  have hu' := evaluate_sound seed 1 1 (by decide) U hu (fun _ _ ↦ rfl) p
  apply hu'.symm.trans
  apply evaluate_sound seed 1 1 (by decide) (fun q ↦ 2 * V q) htwice _ p
  intro q hq
  have h : q = [2] := by simpa [seeds] using hq
  subst q
  exact base

/-- Integration against the marked ψ² sends the actual one-marked raw λ₁² packet
to twice the value of the raw λ₂ packet. -/
theorem raw_integrals {C : StableCurveCohomology ℚ} (A : StrataRealization C 2 (Fin 1))
    (P : PsiClasses C) (I : StableCurveIntegration C) (h : StableArity 2 (Fin 1)) :
    I.integrate 2 (Fin 1) h ((P.psi 2 (Fin 1) h 0) ^ 2 * A.map raw11Degree2) =
    2 * I.integrate 2 (Fin 1) h ((P.psi 2 (Fin 1) h 0) ^ 2 * A.map raw02Degree2) := by
  rw [HodgeDegreeTwoRawRelation.raw_degree_two_equal, two_smul, map_add, mul_add, map_add, two_mul]

/-- Identifying only the two one-marked vertex seeds with integrals of the decoded
strata packets suffices for the comparison at every arity. -/
theorem from_realization {C : StableCurveCohomology ℚ} (A : StrataRealization C 2 (Fin 1))
    (P : PsiClasses C) (I : StableCurveIntegration C) (h : StableArity 2 (Fin 1))
    (U V : List ℕ → ℚ) (hu : Recurrences 1 1 U) (hv : Recurrences 0 2 V)
    (h₁₁ : U [2] = I.integrate 2 (Fin 1) h ((P.psi 2 (Fin 1) h 0) ^ 2 * A.map raw11Degree2))
    (h₀₂ : V [2] = I.integrate 2 (Fin 1) h ((P.psi 2 (Fin 1) h 0) ^ 2 * A.map raw02Degree2))
    (p : List ℕ) : U p = 2 * V p := by
  apply all_powers U V hu hv _ p
  rw [h₁₁, h₀₂, raw_integrals A P I h]

end AxiomaticGW.GKM.HodgeVertexDegreeTwo
