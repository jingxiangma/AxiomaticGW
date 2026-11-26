module

public import AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneReductions
public import AxiomaticGW.GKM.Fixtures.GenusTwoPositivePairClaims

/-! # Matching the complete energy-one frame to the two reconstruction cases

The selection checks both the ordered query and its independently produced value. -/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoEnergyOne

namespace OneBlowup

/-- Reduction index or positive-pair indices for every held row. -/
def selection (i : Fin 52) : Fin 43 ⊕ (Fin 3 × Fin 3) :=
  (#[.inl 0, .inl 1, .inl 2, .inl 3,
    .inl 4, .inl 5, .inr (0, 0), .inl 6,
    .inl 7, .inl 8, .inl 9, .inr (0, 1),
    .inl 10, .inl 11, .inl 12, .inr (0, 2),
    .inl 13, .inl 14, .inl 15, .inl 16,
    .inl 17, .inr (1, 0), .inl 18, .inl 19,
    .inl 20, .inr (1, 1), .inl 21, .inl 22,
    .inr (1, 2), .inl 23, .inl 24, .inl 25,
    .inl 26, .inr (2, 0), .inl 27, .inl 28,
    .inl 29, .inr (2, 1), .inl 30, .inl 31,
    .inr (2, 2), .inl 32, .inl 33, .inl 34,
    .inl 35, .inl 36, .inl 37, .inl 38,
    .inl 39, .inl 40, .inl 41, .inl 42] :
    Array (Fin 43 ⊕ (Fin 3 × Fin 3)))[i.val]'i.isLt

/-- Full request and rational from the selected source. -/
def selectedRow : Fin 43 ⊕ (Fin 3 × Fin 3) → SurfaceQuery .hirzebruchOne × ℚ
  | .inl j => (requests (reductionIndex j), values (reductionIndex j))
  | .inr (a, b) =>
    (GenusTwoPositivePairs.OneBlowup.requests a b, GenusTwoPositivePairs.OneBlowup.values a b)

/-- Every full native query and value agree with their source row. -/
theorem selection_matches : ∀ i : Fin 52,
    selectedRow (selection i) = (requests i, values i) := by decide +kernel

end OneBlowup

namespace TwoBlowups

/-- Reduction index or positive-pair indices for every held row. -/
def selection (i : Fin 240) : Fin 192 ⊕ (Fin 3 × Fin 4 × Fin 4) :=
  (#[.inl 0, .inl 1, .inl 2, .inl 3,
    .inl 4, .inl 5, .inl 6, .inr (2, 0, 0),
    .inl 7, .inl 8, .inl 9, .inl 10,
    .inr (2, 0, 1), .inl 11, .inl 12, .inl 13,
    .inr (2, 0, 2), .inl 14, .inl 15, .inl 16,
    .inr (2, 0, 3), .inl 17, .inl 18, .inl 19,
    .inl 20, .inl 21, .inr (2, 1, 0), .inl 22,
    .inl 23, .inl 24, .inr (2, 1, 1), .inl 25,
    .inl 26, .inr (2, 1, 2), .inl 27, .inl 28,
    .inr (2, 1, 3), .inl 29, .inl 30, .inl 31,
    .inl 32, .inr (2, 2, 0), .inl 33, .inl 34,
    .inl 35, .inr (2, 2, 1), .inl 36, .inl 37,
    .inr (2, 2, 2), .inl 38, .inl 39, .inr (2, 2, 3),
    .inl 40, .inl 41, .inl 42, .inl 43,
    .inr (2, 3, 0), .inl 44, .inl 45, .inl 46,
    .inr (2, 3, 1), .inl 47, .inl 48, .inr (2, 3, 2),
    .inl 49, .inl 50, .inr (2, 3, 3), .inl 51,
    .inl 52, .inl 53, .inl 54, .inl 55,
    .inl 56, .inl 57, .inl 58, .inl 59,
    .inl 60, .inl 61, .inl 62, .inl 63,
    .inl 64, .inl 65, .inl 66, .inl 67,
    .inl 68, .inl 69, .inl 70, .inr (1, 0, 0),
    .inl 71, .inl 72, .inl 73, .inl 74,
    .inr (1, 0, 1), .inl 75, .inl 76, .inl 77,
    .inr (1, 0, 2), .inl 78, .inl 79, .inl 80,
    .inr (1, 0, 3), .inl 81, .inl 82, .inl 83,
    .inl 84, .inl 85, .inr (1, 1, 0), .inl 86,
    .inl 87, .inl 88, .inr (1, 1, 1), .inl 89,
    .inl 90, .inr (1, 1, 2), .inl 91, .inl 92,
    .inr (1, 1, 3), .inl 93, .inl 94, .inl 95,
    .inl 96, .inr (1, 2, 0), .inl 97, .inl 98,
    .inl 99, .inr (1, 2, 1), .inl 100, .inl 101,
    .inr (1, 2, 2), .inl 102, .inl 103, .inr (1, 2, 3),
    .inl 104, .inl 105, .inl 106, .inl 107,
    .inr (1, 3, 0), .inl 108, .inl 109, .inl 110,
    .inr (1, 3, 1), .inl 111, .inl 112, .inr (1, 3, 2),
    .inl 113, .inl 114, .inr (1, 3, 3), .inl 115,
    .inl 116, .inl 117, .inl 118, .inl 119,
    .inl 120, .inl 121, .inl 122, .inl 123,
    .inl 124, .inl 125, .inl 126, .inl 127,
    .inl 128, .inl 129, .inl 130, .inl 131,
    .inl 132, .inl 133, .inl 134, .inr (0, 0, 0),
    .inl 135, .inl 136, .inl 137, .inl 138,
    .inr (0, 0, 1), .inl 139, .inl 140, .inl 141,
    .inr (0, 0, 2), .inl 142, .inl 143, .inl 144,
    .inr (0, 0, 3), .inl 145, .inl 146, .inl 147,
    .inl 148, .inl 149, .inr (0, 1, 0), .inl 150,
    .inl 151, .inl 152, .inr (0, 1, 1), .inl 153,
    .inl 154, .inr (0, 1, 2), .inl 155, .inl 156,
    .inr (0, 1, 3), .inl 157, .inl 158, .inl 159,
    .inl 160, .inr (0, 2, 0), .inl 161, .inl 162,
    .inl 163, .inr (0, 2, 1), .inl 164, .inl 165,
    .inr (0, 2, 2), .inl 166, .inl 167, .inr (0, 2, 3),
    .inl 168, .inl 169, .inl 170, .inl 171,
    .inr (0, 3, 0), .inl 172, .inl 173, .inl 174,
    .inr (0, 3, 1), .inl 175, .inl 176, .inr (0, 3, 2),
    .inl 177, .inl 178, .inr (0, 3, 3), .inl 179,
    .inl 180, .inl 181, .inl 182, .inl 183,
    .inl 184, .inl 185, .inl 186, .inl 187,
    .inl 188, .inl 189, .inl 190, .inl 191] :
    Array (Fin 192 ⊕ (Fin 3 × Fin 4 × Fin 4)))[i.val]'i.isLt

/-- Full request and rational from the selected source. -/
def selectedRow : Fin 192 ⊕ (Fin 3 × Fin 4 × Fin 4) → SurfaceQuery .blowupTwo × ℚ
  | .inl j => (requests (reductionIndex j), values (reductionIndex j))
  | .inr (0, a, b) =>
    (GenusTwoPositivePairs.ExceptionalOne.requests a b,
      GenusTwoPositivePairs.ExceptionalOne.values a b)
  | .inr (1, a, b) =>
    (GenusTwoPositivePairs.ExceptionalTwo.requests a b,
      GenusTwoPositivePairs.ExceptionalTwo.values a b)
  | .inr (2, a, b) =>
    (GenusTwoPositivePairs.StrictLine.requests a b,
      GenusTwoPositivePairs.StrictLine.values a b)

/-- Every full native query and value agree with their source row. -/
theorem selection_matches : ∀ i : Fin 240,
    selectedRow (selection i) = (requests i, values i) := by decide +kernel

end TwoBlowups

end AxiomaticGW.GKM.GenusTwoEnergyOne
