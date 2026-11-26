module

public import AxiomaticGW.GKM.SurfaceLocalizationEdge

/-! # Deformation and obstruction factors for multiple covers -/

@[expose] public section
namespace AxiomaticGWTest.GKM.SurfaceLocalizationEdge
open AxiomaticGW.GKM.SurfaceLocalizationEdge

/-- With two sheets, a normal degree of +1 contributes three denominator factors,
degree zero contributes one, and degree −1 contributes one numerator factor. -/
example : factor? 2 (4 : ℚ) 7 1 = some (1/6720) ∧
    factor? 2 (4 : ℚ) 7 0 = some (1/448) ∧
    factor? 2 (4 : ℚ) 7 (-1) = some (9/64) := by decide +kernel

/-- A zero obstruction character gives a zero contribution. A zero deformation or tangent
weight makes the contribution undefined. -/
example : factor? 2 (4 : ℚ) (-2) (-1) = some 0 ∧
    factor? 2 (4 : ℚ) 2 1 = none ∧ factor? 2 (0 : ℚ) 2 0 = none := by decide +kernel

/-- The reversed orientation of a degree-three cover has the same signed contribution. -/
example : factor? 3 (-6 : ℚ) 4 (-1) = factor? 3 (6 : ℚ) (-2) (-1) := by
  rw [show (4 : ℚ) = -2 - ((-1 : ℤ) : ℚ) * 6 by decide +kernel]
  exact factor_reverse 3 (6 : ℚ) (-2) (-1)

end AxiomaticGWTest.GKM.SurfaceLocalizationEdge
