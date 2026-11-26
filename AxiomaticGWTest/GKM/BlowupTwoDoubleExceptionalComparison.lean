import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleExceptionalCompleteReplay

/-! # Doubled exceptional comparisons on the projected and original targets -/

namespace AxiomaticGWTest.GKM.BlowupTwoDoubleExceptionalComparison
open AxiomaticGW AxiomaticGW.GKM
open BlowupTwoDoubleExceptionalFewMarkings

/-- The two cotangent powers on 2E₁ match the original F₁ evaluator on its own full class. -/
theorem interior :
    requests 112 = ⟨2, ![2, 0, 0], [⟨.unit, 2⟩, ⟨.unit, 3⟩]⟩ ∧
    equivariant 112 = 27/1280 ∧ SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0
      (X := .hirzebruchOne) ⟨2, ![2, 0], [⟨.unit, 2⟩, ⟨.unit, 3⟩]⟩ (27/1280) := by
  have h := matched 112 (.inr 2) (by decide +kernel)
  refine ⟨by decide +kernel, h.2.2.trans ?_, ?_⟩
  · have hv : (sourceRow (.inr 2)).2 = 27/1280 := by decide +kernel
    rw [hv]
    norm_num
  · exact h.2.1

/-- On 2E₂ an E₁ insertion fails the ordinary label projection and gives native field zero. -/
theorem foreign :
    requests 81 = ⟨2, ![0, 2, 0], [⟨.exceptional 1, 2⟩, ⟨.exceptional 0, 1⟩]⟩ ∧
    project? (requests 81) = none ∧ equivariant 81 = 0 :=
  ⟨by decide +kernel, unmatched 81 (by decide +kernel)⟩

/-- The primary E₂ and fourth unit descendant on 2E₂ use both terms of the divisor equation. -/
theorem target_divisor :
    requests 70 = ⟨2, ![0, 2, 0], [⟨.exceptional 1, 0⟩, ⟨.unit, 4⟩]⟩ ∧
    SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 (X := .blowupTwo)
      ⟨2, ![0, 2, 0], [⟨.exceptional 1, 0⟩, ⟨.unit, 4⟩]⟩ (1/384) ∧
    equivariant 70 = 1/384 ∧
    EquivariantCoefficients.Specializes (equivariant 70) (1/384) := by
  have h := target_certified (j := 70) (by decide +kernel)
  have hq : requests 70 = ⟨2, ![0, 2, 0], [⟨.exceptional 1, 0⟩, ⟨.unit, 4⟩]⟩ := by decide +kernel
  have hv : values 70 = 1/384 := by decide +kernel
  rw [hq, hv] at h
  exact ⟨hq, h.1, h.2.1.trans (by norm_num), h.2.2⟩

/-- The positive-positive pair on the second axis has the negative sign from the original
mixed reconstruction, and its complete incoming field is the same rational. -/
theorem own_second_interior :
    requests 84 = ⟨2, ![0, 2, 0], [⟨.exceptional 1, 1⟩, ⟨.exceptional 1, 2⟩]⟩ ∧
    SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 (requests 84) (-7/160) ∧
    equivariant 84 = -7/160 := by
  have hv : values 84 = -7/160 := by decide +kernel
  refine ⟨by decide +kernel, hv ▸ accepted 84, ?_⟩
  rw [(certified 84).2.1, hv]
  norm_num

end AxiomaticGWTest.GKM.BlowupTwoDoubleExceptionalComparison
