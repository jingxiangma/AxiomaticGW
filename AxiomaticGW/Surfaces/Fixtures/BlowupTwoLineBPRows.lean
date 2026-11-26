/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineBPConstants
public import AxiomaticGW.Surfaces.GenusTwoBlowupBoundedCertificate
public import AxiomaticGW.Surfaces.GenusTwoBPCoefficientSymmetry

/-!
# Genus-two BP equations at the strict transform of the two-point line

The complete energy-one grid contains the classes 0, E₁, E₂ and L. At the
established plane-degree-zero boundary only H₀, K₁,₀ and K₂,₀ contribute.
The BP rows P, K₁ and K₂ cancel there against their lower-genus constants.
Their remaining coefficients identify P and both K descendants with H at L.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineBP
open SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction SurfaceGenusTwoBlowupScalar
open SurfaceGenusTwoBlowupBoundedCertificate

private abbrev X := SurfaceTarget.blowupTwo
private def curves : Fin 4 → X.Curve := ![0, X.exceptionalCurve 0, X.exceptionalCurve 1, line]
/-- Order of the complete five-column canonical grid on the two-point blowup. -/
def canonicalFamily : Fin 5 → Family .blowupTwo := ![.hyperplane, .point, .primary, .exceptional 0,
  .exceptional 1]
private def rows : Fin 3 → Family X := ![.point, .exceptional 0, .exceptional 1]
private def column (k : Fin 4 × Fin 5) : Variable X :=
  .inr ((canonicalFamily k.2).query (curves k.1))

private theorem grid : columns (states X 1) = Finset.univ.image column := by decide +kernel
private theorem distinct : Function.Injective column := by
  change ∀ k l, column k = column l → k = l
  decide +kernel

private def coeff (r : Fin 3) (c : Fin 4) (b : Fin 5) : ℚ :=
  singletonCoefficient 0 (line, rows r) (column (c, b))

private def sameClass : Fin 3 → Fin 5 → ℚ :=
  ![![18, -18, 0, 0, 0], ![0, 18, 0, -18, 0], ![0, 18, 0, 0, -18]]

-- Each coefficient uses only the four BP diagrams with a genus-two vertex.
set_option Elab.async false
set_option maxRecDepth 20000

private def rowLabel : Fin 3 → SurfaceBasisLabel X := ![.hyperplane, .exceptional 0, .exceptional 1]

private theorem coeff_paperSum (r : Fin 3) (c : Fin 4) (b : Fin 5) :
    coeff r c b = ∑ i : Fin 4, BelorousskiPandharipande.rawPaperCoefficient (Fin.castAdd 16 i) *
      (6 * SurfaceGenusTwo.pointCoefficient X (column (c, b))
        (BelorousskiPandharipande.paperCotangentTerm (Fin.castAdd 16 i)) line 0
          (fun _ ↦ rowLabel r)) := by
  have h (a : SurfaceBasisLabel X) : (![a, a, a] : Fin 3 → _) = fun _ ↦ a := by
    funext k
    fin_cases k <;> rfl
  have he : X.effective.energy line = 1 := by decide +kernel
  rw [← BelorousskiPandharipande.pointCoefficient_eq_six_paperSum, ← h]
  have hc (a : SurfaceBasisLabel X) :
      BelorousskiPandharipande.pointCoefficient X (X.effective.energy line - 1)
        line ![a, a, a] (column (c, b)) =
      BelorousskiPandharipande.pointCoefficient X 0 line ![a, a, a] (column (c, b)) := by
    rw [he, Nat.sub_self]
  fin_cases r
  · exact hc .hyperplane
  · exact hc (.exceptional 0)
  · exact hc (.exceptional 1)

private theorem zero_coeff (r : Fin 3) (b : Fin 5) :
    coeff r 0 b = ![12, 0, -12, -12, -12] b := by
  rw [coeff_paperSum]
  revert r b
  decide +kernel

private theorem line_coeff (r : Fin 3) (b : Fin 5) : coeff r 3 b = sameClass r b := by
  rw [coeff_paperSum]
  revert r b
  decide +kernel

private abbrev value := SurfaceGenusTwoBlowupRecursion.values (X := X) 0

private theorem boundary_zero (b : Fin 5) : value (curves 0, canonicalFamily b) =
    ![-1 / 960, 0, 0, -1 / 2880, -1 / 2880] b := by
  unfold value
  rw [SurfaceGenusTwoBlowupRecursion.values_boundary 0 (curves 0, canonicalFamily b) (map_zero _)]
  revert b
  decide +kernel

private theorem boundary_exceptional (i : Fin 2) (b : Fin 5) :
    value (X.exceptionalCurve i, canonicalFamily b) = 0 := by
  unfold value
  rw [SurfaceGenusTwoBlowupRecursion.values_boundary 0 (X.exceptionalCurve i, canonicalFamily b)
    (X.planeDegree_exceptionalCurve i)]
  exact SurfaceGenusTwoBlowupBoundary.value_of_ne_zero _ (X.exceptionalCurve_ne_zero i) _

private theorem constant_rows (r : Fin 3) : constant 0 (line, rows r) = 1 / 240 := by
  fin_cases r
  · exact point_constant
  · exact exceptional_constant 0
  · exact exceptional_constant 1

/-- Every original row at L reduces to its class-zero and same-class columns.
The two exceptional classes at energy one have zero boundary values. -/
theorem reduced_row (f : Family .blowupTwo) :
    constant 0 (line, f) +
      ((∑ b : Fin 5, singletonCoefficient 0 (line, f) (.inr ((canonicalFamily b).query 0)) *
          (![-1 / 960, 0, 0, -1 / 2880, -1 / 2880] : Fin 5 → ℚ) b) +
        ∑ b : Fin 5, singletonCoefficient 0 (line, f) (.inr ((canonicalFamily b).query line)) *
          SurfaceGenusTwoBlowupRecursion.values 0 (line, canonicalFamily b)) = 0 := by
  have hp : 0 < X.planeDegree line := by decide +kernel
  have hs : (line, f) ∈ states X 1 :=
    (mem_states X 1 _).mpr (by change X.effective.energy line ≤ 1; decide +kernel)
  have he := (replay_eq_row 0 1 (line, f) (canonicalValuation value) hs hp).trans
    (SurfaceGenusTwoBlowupRecursion.values_equations 0 _ hp)
  have hg (c x : ℚ) : (if x = 0 then 0 else c * x) = c * x := by
    split_ifs with h
    · rw [h, mul_zero]
    · rfl
  rw [SurfaceGenusTwoBlowupScalar.replay, grid, Finset.sum_image
    (fun _ _ _ _ h ↦ distinct h), Fintype.sum_prod_type] at he
  simp only [hg, column, canonicalValuation_query] at he
  change constant 0 (line, f) + (∑ c : Fin 4, ∑ b : Fin 5,
    singletonCoefficient 0 (line, f) (.inr ((canonicalFamily b).query (curves c))) *
      value (curves c, canonicalFamily b)) = 0 at he
  have h₁ (b : Fin 5) : value (curves 1, canonicalFamily b) = 0 := boundary_exceptional 0 b
  have h₂ (b : Fin 5) : value (curves 2, canonicalFamily b) = 0 := boundary_exceptional 1 b
  rw [Fin.sum_univ_four] at he
  simp only [boundary_zero, h₁, h₂, mul_zero, Finset.sum_const_zero, add_zero] at he
  rw [show curves 0 = 0 from rfl, show curves 3 = line from rfl] at he
  exact he

private theorem equation (r : Fin 3) :
    (∑ b : Fin 5, sameClass r b * value (line, canonicalFamily b)) = 0 := by
  have he := reduced_row (rows r)
  change constant 0 (line, rows r) + ((∑ b : Fin 5,
    coeff r 0 b * (![-1 / 960, 0, 0, -1 / 2880, -1 / 2880] : Fin 5 → ℚ) b) +
    ∑ b : Fin 5, coeff r 3 b * value (line, canonicalFamily b)) = 0 at he
  simp only [constant_rows, zero_coeff, line_coeff] at he
  have hc : (∑ b : Fin 5, (![12, 0, -12, -12, -12] : Fin 5 → ℚ) b *
      (![-1 / 960, 0, 0, -1 / 2880, -1 / 2880] : Fin 5 → ℚ) b) = -1 / 240 := by
    decide +kernel
  rw [hc] at he
  change (1 / 240 : ℚ) + (-1 / 240 +
    ∑ b : Fin 5, sameClass r b * value (line, canonicalFamily b)) = 0 at he
  linarith

/-- The complete HHH row identifies the reconstructed point and hyperplane descendants at L. -/
theorem point_eq_hyperplane : SurfaceGenusTwoBlowupRecursion.values 0 (line, .point) =
    SurfaceGenusTwoBlowupRecursion.values 0 (line, .hyperplane) := by
  have he := equation 0
  rw [Fin.sum_univ_five] at he
  change
    18 * value (line, .hyperplane) +
    -18 * value (line, .point) +
    0 * value (line, .primary) +
    0 * value (line, .exceptional 0) +
    0 * value (line, .exceptional 1) = 0 at he
  linarith only [he]

/-- Both complete all-exceptional rows identify their separate descendants with P at L. -/
theorem exceptional_eq_point (j : Fin 2) :
    SurfaceGenusTwoBlowupRecursion.values 0 (line, .exceptional j) =
      SurfaceGenusTwoBlowupRecursion.values 0 (line, .point) := by
  fin_cases j
  · change value (line, .exceptional 0) = value (line, .point)
    have he := equation 1
    rw [Fin.sum_univ_five] at he
    change
      0 * value (line, .hyperplane) +
      18 * value (line, .point) +
      0 * value (line, .primary) +
      -18 * value (line, .exceptional 0) +
      0 * value (line, .exceptional 1) = 0 at he
    linarith only [he]
  · change value (line, .exceptional 1) = value (line, .point)
    have he := equation 2
    rw [Fin.sum_univ_five] at he
    change
      0 * value (line, .hyperplane) +
      18 * value (line, .point) +
      0 * value (line, .primary) +
      0 * value (line, .exceptional 0) +
      -18 * value (line, .exceptional 1) = 0 at he
    linarith only [he]

end AxiomaticGW.BlowupTwoLineBP
