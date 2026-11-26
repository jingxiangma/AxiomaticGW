/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Transfer
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineBPRows

/-! # The complete original BP equations at the two rulings of the two-point blowup

The HHH and two exceptional triples have canonical support at effective subclasses.
Each ruling has four such subclasses. The two nonzero proper
classes already have vanishing canonical families, leaving only class zero and the
full ruling in the three equations.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.BP
open SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupBoundedCertificate
open SurfaceGenusTwoBlowupScalar SurfacePolynomialReduction
open _root_.AxiomaticGW.BlowupTwoLineBP (canonicalFamily)

/-- The constant, exceptional, strict-line and full ruling classes in the degree splittings. -/
def subcurve (i : Fin 2) : Fin 4 → X.Curve :=
  ![0, X.exceptionalCurve i, BlowupTwoLineBP.line, curve i]
/-- The point row followed by both absolute exceptional rows. -/
def row : Fin 3 → Family X := ![.point, .exceptional 0, .exceptional 1]
/-- All five canonical sectors at the four possible classes. -/
def grid (i : Fin 2) : List (State X) :=
  (List.ofFn (subcurve i)).flatMap fun b ↦ (families X).map fun f ↦ (b, f)

private theorem subcurve_mem (i : Fin 2) (c d : X.Curve) (h : c + d = curve i) :
    c ∈ List.ofFn (subcurve i) := by
  have hm : (c, d) ∈ X.effective.splittings (curve i) :=
    (X.effective.mem_splittings _ _ _).mpr h
  have all : ∀ t ∈ X.effective.splittings (curve i), t.1 ∈ List.ofFn (subcurve i) := by
    rw [← X.splittings_eq]
    fin_cases i <;> decide +kernel
  exact all (c, d) hm

private theorem grid_cover (i : Fin 2) (r : Fin 3) (v : Variable X)
    (hv : v ∈ (RationalTerms.collect
      (SurfaceGenusTwoBlowupRecursion.row 0 (curve i, row r))).bind Prod.snd) :
    v ∈ columns (grid i) := by
  obtain ⟨t, ht, hv⟩ := Multiset.mem_bind.mp hv
  have sup : t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ c ∈ SurfaceGenusTwo.canonicalQueries X gamma,
      t.2 = {Sum.inr c} ∧ ∃ delta : X.Curve, gamma + delta = curve i := by
    fin_cases r
    all_goals
      exact BelorousskiPandharipande.collected_normalized_primary_canonical_support
        (X.effective.energy (curve i) - 1) (curve i) _ ht
  rcases sup with h | ⟨g, c, hc, h, δ, hg⟩
  · simp only [h, Multiset.notMem_zero] at hv
  · rw [h, Multiset.mem_singleton] at hv
    obtain ⟨f, hf⟩ := family_of_mem_canonicalQueries hc
    apply (mem_columns _ _).mpr
    refine ⟨(g, f), List.mem_flatMap.mpr ⟨g, subcurve_mem i g δ hg, ?_⟩, ?_⟩
    · exact List.mem_map.mpr ⟨f, mem_families X f, rfl⟩
    · simpa only [hf] using hv

private def col (i : Fin 2) (t : Fin 4 × Fin 5) : Variable X :=
  .inr ((canonicalFamily t.2).query (subcurve i t.1))

private theorem columns_eq (i : Fin 2) : columns (grid i) = Finset.univ.image (col i) := by
  fin_cases i <;> decide +kernel

private theorem columns_injective (i : Fin 2) : Function.Injective (col i) := by
  change ∀ t s, col i t = col i s → t = s
  fin_cases i <;> decide +kernel

/-- The existing reconstructed canonical family at pivot zero. -/
abbrev actual := SurfaceGenusTwoBlowupRecursion.values (X := X) 0
/-- The original constant-class divisor seeds in the canonical order H, P, N, E₁, E₂. -/
def zeroValues : Fin 5 → ℚ := ![-1/960, 0, 0, -1/2880, -1/2880]
private theorem primitive (i : Fin 2) (b : Fin 5) :
    actual (X.exceptionalCurve i, canonicalFamily b) = 0 ∧
      actual (BlowupTwoLineBP.line, canonicalFamily b) = 0 := by
  have hE : X.effective.energy (X.exceptionalCurve i) ≤ 1 := by fin_cases i <;> decide +kernel
  unfold actual
  rw [BlowupTwoLineTable.values_eq (X.exceptionalCurve i, canonicalFamily b) hE,
    BlowupTwoLineTable.values_eq (BlowupTwoLineBP.line, canonicalFamily b)
      (by change X.effective.energy BlowupTwoLineBP.line ≤ 1; decide +kernel)]
  fin_cases i <;> fin_cases b <;> decide +kernel
private theorem at_zero (b : Fin 5) : actual (0, canonicalFamily b) = zeroValues b := by
  unfold actual
  rw [SurfaceGenusTwoBlowupRecursion.values_boundary _ _ (map_zero _)]
  fin_cases b <;> decide +kernel

/-- Every original BP equation reduces to its five class-zero and five full-class coefficients. -/
theorem reduced_row (i : Fin 2) (r : Fin 3) :
    constant 0 (curve i, row r) +
      ((∑ b : Fin 5, singletonCoefficient 0 (curve i, row r) (.inr ((canonicalFamily b).query 0)) *
        zeroValues b) +
      ∑ b : Fin 5, singletonCoefficient 0 (curve i, row r)
        (.inr ((canonicalFamily b).query (curve i))) *
          actual (curve i, canonicalFamily b)) = 0 := by
  have hp : 0 < X.planeDegree (curve i) := by fin_cases i <;> decide +kernel
  have he := (SurfaceGenusTwoBlowupScalar.replay_eq_row 0 (curve i, row r)
    (canonicalValuation actual) (grid i) (grid_cover i r)).trans
    (SurfaceGenusTwoBlowupRecursion.values_equations 0 _ hp)
  have hz (c x : ℚ) : (if x = 0 then 0 else c * x) = c * x := by
    split_ifs with h
    · rw [h, mul_zero]
    · rfl
  rw [replay, columns_eq, Finset.sum_image (fun _ _ _ _ h ↦ columns_injective i h),
    Fintype.sum_prod_type] at he
  simp only [hz, col, canonicalValuation_query] at he
  have h₀ (b : Fin 5) : actual (subcurve i 0, canonicalFamily b) = zeroValues b := at_zero b
  have h₁ (b : Fin 5) : actual (subcurve i 1, canonicalFamily b) = 0 := (primitive i b).1
  have h₂ (b : Fin 5) : actual (subcurve i 2, canonicalFamily b) = 0 := (primitive i b).2
  rw [Fin.sum_univ_four] at he
  simp only [h₀, h₁, h₂, mul_zero, Finset.sum_const_zero, add_zero] at he
  exact he
end AxiomaticGW.BlowupTwoRuling.BP
