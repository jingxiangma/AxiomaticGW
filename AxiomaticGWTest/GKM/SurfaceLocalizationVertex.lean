module

public import AxiomaticGW.GKM.SurfaceLocalizationVertex

/-! # Positive-edge and contracted vertex conventions -/

@[expose] public section
namespace AxiomaticGWTest.GKM.SurfaceLocalizationVertex
open AxiomaticGW.GKM.SurfaceLocalizationVertex

/-- The flag sign changes with the parity of a descendant at an unstable rational end. -/
example : factor? (fun _ ↦ 0) 0 [] (2 : ℚ) 3 [2] = some (1/3) ∧
    factor? (fun _ ↦ 0) 0 [1] (2 : ℚ) 3 [2] = some (-1/3) ∧
    factor? (fun _ ↦ 0) 0 [2] (2 : ℚ) 3 [2] = some (2/3) ∧
    factor? (fun _ ↦ 0) 0 [] (2 : ℚ) 3 [2,3] = some (1/30) := by decide +kernel

/-- Each inverse must have a nonzero denominator, including the smoothing of a bivalent node. -/
example : factor? (fun _ ↦ 0) 0 [] (2 : ℚ) 3 [2,-2] = none ∧
    factor? (fun _ ↦ 0) 0 [] (0 : ℚ) 3 [2] = none ∧
    factor? (fun _ ↦ 0) 2 [3] (2 : ℚ) 0 [-2,-2] = none ∧
    factor? (fun _ ↦ 0) 1 [0] (2 : ℚ) 3 [0] = none := by decide +kernel

/-- The two unstable contracted ranges and the genus bound are checked at the public entry point. -/
example : factor? (fun _ ↦ 0) 0 [0,0] (2 : ℚ) 3 [] = none ∧
    factor? (fun _ ↦ 0) 1 [] (2 : ℚ) 3 [] = none ∧
    factor? (fun _ ↦ 0) 3 [1] (2 : ℚ) 3 [2] = none := by decide +kernel

end AxiomaticGWTest.GKM.SurfaceLocalizationVertex
