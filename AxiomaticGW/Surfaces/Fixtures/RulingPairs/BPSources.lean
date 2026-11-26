/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.BPFrame
public import AxiomaticGW.Surfaces.GenusTwoFirstCoefficients
public import AxiomaticGW.Surfaces.GenusTwoBPCoefficientSymmetry

/-! # Original BP coefficient contractions on the two ruling classes

For a class-zero column the whole ruling remains available to the rational
complement. For a full-class column its remaining class is zero. First
descendants use their proved exact-class pruning before the four original
genus-two coefficient diagrams are contracted.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.BP
open SurfaceGenusTwo SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupScalar
open BelorousskiPandharipande SurfacePolynomialReduction
open _root_.AxiomaticGW.BlowupTwoLineBP (canonicalFamily)

/-- The three repeated external states of each unshifted BP equation. -/
def rowLabel : Fin 3 → SurfaceBasisLabel X := ![.hyperplane, .exceptional 0, .exceptional 1]

/-- The only two classes carrying potentially nonzero values after the primitive tables. -/
def columnCurve (i : Fin 2) (full : Bool) : X.Curve := if full then curve i else 0

/-- The complete canonical variable of a retained column. -/
def variableAt (i : Fin 2) (full : Bool) (b : Fin 5) : Variable X :=
  .inr ((canonicalFamily b).query (columnCurve i full))

/-- The full normalized vertex or its proved first-descendant specialization. -/
def terminal (i : Fin 2) (full : Bool) (j : Fin 5) : SurfaceVertexValues X ℚ :=
  let c := columnCurve i full
  let n := X.effective.energy c
  match canonicalFamily j with
  | .hyperplane => firstCoefficientVertex X c .hyperplane n
  | .point => firstCoefficientVertex X c .point (n - 1)
  | .exceptional k => firstCoefficientVertex X c (.exceptional k) n
  | .primary => coefficientVertex X (variableAt i full j)

private theorem terminal_eq (i : Fin 2) (full : Bool) (j : Fin 5) :
    terminal i full j = coefficientVertex X (variableAt i full j) := by
  fin_cases j
  all_goals first | exact firstCoefficientVertex_eq _ _ _ | rfl

/-- Each original BP diagram at the remaining effective class. -/
def diagram (i : Fin 2) (r : Fin 3) (full : Bool) (j : Fin 5) (k : Fin 4) : ℚ :=
  remainderPointCoefficient X (variableAt i full j) (terminal i full j)
    (paperCotangentTerm (Fin.castAdd 16 k)) (if full then 0 else curve i) 1 (fun _ ↦ rowLabel r)

/-- The sixteen rational-elliptic sources of the constant, using the original point functions. -/
def lowerConstant (i : Fin 2) (r : Fin 3) : ℚ :=
  6 * ∑ k : Fin 16, rawPaperCoefficient (Fin.natAdd 4 k) *
    SurfaceGenusOne.primaryGraphDimensionEval X (SurfacePointBenchmarkCache.genusZero X)
      (SurfacePointBenchmarkCache.genusOne X) (paperTerm (Fin.natAdd 4 k)).1
      (curve i) 1 (fun _ ↦ rowLabel r)

private theorem triple (a : SurfaceBasisLabel X) : (![a, a, a] : Fin 3 → _) = fun _ ↦ a := by
  funext t
  fin_cases t <;> rfl

/-- The original constant of every unshifted ruling BP row. -/
theorem constant_eq (i : Fin 2) (r : Fin 3) :
    constant 0 (curve i, row r) = lowerConstant i r := by
  have he : X.effective.energy (curve i) = 2 := by fin_cases i <;> decide +kernel
  rw [← SurfaceGenusTwoBlowupPointCache.constant_eq 0 (curve i, row r)
    (SurfacePointBenchmarkCache.genusZero X) (SurfacePointBenchmarkCache.genusOne X)
    (SurfacePointBenchmarkCache.genusZero_eq X) (SurfacePointBenchmarkCache.genusOne_eq X)]
  fin_cases r
  all_goals
    simp only [row, SurfaceGenusTwoBlowupPointCache.constant, he, Nat.reduceSub, triple]
    exact lowerPointConstantWithPrimary_eq_six_primaryGraphSum _ _ _ _ _ _

/-- The exact original singleton coefficient, including the six permutations of each triple. -/
theorem coefficient_eq (i : Fin 2) (r : Fin 3) (full : Bool) (j : Fin 5) :
    singletonCoefficient 0 (curve i, row r) (variableAt i full j) =
      ∑ k : Fin 4, rawPaperCoefficient (Fin.castAdd 16 k) * (6 * diagram i r full j k) := by
  have he : X.effective.energy (curve i) = 2 := by fin_cases i <;> decide +kernel
  have eqRow : singletonCoefficient 0 (curve i, row r) (variableAt i full j) =
      BelorousskiPandharipande.pointCoefficient X 1 (curve i) (fun _ ↦ rowLabel r)
        (variableAt i full j) := by
    fin_cases r
    all_goals
      simp only [row, rowLabel, singletonCoefficient, he, Nat.reduceSub, triple]
      rfl
  have hv : SurfaceGenusZero.variableCurve (variableAt i full j) = columnCurve i full := by
    fin_cases j <;> rfl
  have hs : SurfaceGenusZero.variableCurve (variableAt i full j) +
      (if full then 0 else curve i) = curve i := by
    rw [hv]
    cases full <;> simp only [columnCurve, Bool.false_eq_true, if_false, if_true, zero_add,
      add_zero]
  rw [eqRow, pointCoefficient_eq_six_paperSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [diagram, remainderPointCoefficient_eq X _ _ (terminal_eq i full j), hs]

end AxiomaticGW.BlowupTwoRuling.BP
