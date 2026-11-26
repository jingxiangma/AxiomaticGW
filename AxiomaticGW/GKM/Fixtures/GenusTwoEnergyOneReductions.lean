module

public import AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneClaims
public import AxiomaticGW.GKM.Fixtures.BlowupTwoLineCompletedReplay
public import AxiomaticGW.GKM.Fixtures.BlowupTwoLinePointUnitSquareReplay
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLinePointDivisors

/-! # Singleton, primary-point, string, dilaton and divisor rows at energy one

The complementary frame has two insertions of total complex codimension two each
with positive cotangent powers. Every selected row below has its own arithmetic proof.
The binding checks the full request and rational answer against the native frame. -/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoEnergyOne
open SurfaceGenusTwoBlowupDescendants

private abbrev ProvenRow {X : SurfaceTarget} (i : Fin X.blowups) :=
  {p : SurfaceQuery X × ℚ // CheckedDescendant i p.1 p.2}

private def verified {X : SurfaceTarget} {i : Fin X.blowups} {q : SurfaceQuery X} {v : ℚ}
    (h : CheckedDescendant i q v) : ProvenRow i := ⟨(q, v), h⟩

namespace OneBlowup

/-- Original indices of the singleton, primary-point and marked-equation rows. -/
def reductionIndex (i : Fin 43) : Fin 52 :=
  (#[0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18,
    19, 20, 22, 23, 24, 26, 27, 29, 30, 31, 32, 34, 35, 36, 38, 39,
    41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51] :
    Array (Fin 52))[i.val]'i.isLt

private def rows (i : Fin 43) : ProvenRow (X := .hirzebruchOne) 0 :=
  (#[verified (.mixed (GenusTwoOneMarking.OneBlowup.accepted 0)),
    verified (.mixed (GenusTwoOneMarking.OneBlowup.accepted 1)),
    verified (.mixed (GenusTwoOneMarking.OneBlowup.accepted 2)),
    verified (.exceptionalPoint (q := requests 3) (v := 0) (by decide +kernel)),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 0 0).2),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 0 2).2),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 0 3).2),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 0 1).2),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 1 0).2),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 1 2).2),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 0 0 1).2),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 2 0).2),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 2 2).2),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 0 1 1).2),
    verified (.exceptionalPoint (q := requests 17) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 18) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 19) (v := 0) (by decide +kernel)),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 0 0 0).2),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 1 3).2),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 1 0 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 1 0 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 2 0 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 1 1 1).2),
    verified (.exceptionalPoint (q := requests 30) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 31) (v := 0) (by decide +kernel)),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 0 1 0).2),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 2 3).2),
    verified (.unitPair (GenusTwoUnitPairs.OneBlowup.accepted 2 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 1 1 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 2 0 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 2 1 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.OneBlowup.accepted 2 1 1).2),
    verified (.exceptionalPoint (q := requests 42) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 43) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 44) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 45) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 46) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 47) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 48) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 49) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 50) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 51) (v := 0) (by decide +kernel))] :
    Array (ProvenRow (X := .hirzebruchOne) 0))[i.val]'i.isLt

private theorem binding : ∀ i : Fin 43, (rows i).val =
    (requests (reductionIndex i), values (reductionIndex i)) := by decide +kernel

/-- Each selected ordinary specialization has an original geometric reconstruction route. -/
theorem reductions_accepted (i : Fin 43) :
    CheckedDescendant 0 (requests (reductionIndex i)) (values (reductionIndex i)) := by
  have h := (rows i).property
  rwa [binding i] at h

end OneBlowup

namespace TwoBlowups

/-- Original indices of the singleton, primary-point and marked-equation rows. -/
def reductionIndex (i : Fin 192) : Fin 240 :=
  (#[0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 17, 18,
    19, 21, 22, 23, 24, 25, 27, 28, 29, 31, 32, 34, 35, 37, 38, 39,
    40, 42, 43, 44, 46, 47, 49, 50, 52, 53, 54, 55, 57, 58, 59, 61,
    62, 64, 65, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
    80, 81, 82, 83, 84, 85, 86, 88, 89, 90, 91, 93, 94, 95, 97, 98,
    99, 101, 102, 103, 104, 105, 107, 108, 109, 111, 112, 114, 115, 117, 118, 119,
    120, 122, 123, 124, 126, 127, 129, 130, 132, 133, 134, 135, 137, 138, 139, 141,
    142, 144, 145, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
    160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 173, 174, 175, 177, 178,
    179, 181, 182, 183, 184, 185, 187, 188, 189, 191, 192, 194, 195, 197, 198, 199,
    200, 202, 203, 204, 206, 207, 209, 210, 212, 213, 214, 215, 217, 218, 219, 221,
    222, 224, 225, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239] :
    Array (Fin 240))[i.val]'i.isLt

private def rows (i : Fin 192) : ProvenRow (X := .blowupTwo) 0 :=
  (#[verified (.mixed (BlowupTwoLineOneMarkingReplay.all_accepted 0)),
    verified (.mixed (BlowupTwoLineOneMarkingReplay.all_accepted 1)),
    verified (.mixed (BlowupTwoLineOneMarkingReplay.all_accepted 2)),
    verified (.mixed (BlowupTwoLineOneMarkingReplay.all_accepted 3)),
    verified (.mixed (BlowupTwoLineOneMarkingReplay.all_accepted 4)),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 0 0).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 0 2).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 0 3).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 0 1).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 1 0).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 1 2).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 0 0 1).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 2 0).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 2 2).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 0 1 1).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 3 0).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 3 2).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 0 2 1).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLinePoint.accepted 0 0).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLinePoint.accepted 0 2).2),
    verified (.mixed (BlowupTwoLinePointUnitSquare.accepted 1)),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 0 0 0).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 1 3).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 1 0 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 1 0 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 2 0 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 1 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 3 0 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 1 2 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 4 0 0).2),
    verified (.mixed (BlowupTwoLinePointDivisors.value 0 false)),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 0 1 0).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 2 3).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 2 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 1 1 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 2 0 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 2 1 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 2 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 3 1 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 2 2 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 4 1 0).2),
    verified (.mixed (BlowupTwoLinePointDivisors.value 1 false)),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 0 2 0).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 3 3).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLine.accepted 3 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 1 2 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 3 0 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 2 2 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 3 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 3 2 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 3 2 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 4 2 0).2),
    verified (.mixed (BlowupTwoLinePointDivisors.value 2 false)),
    verified (.mixed (BlowupTwoLinePointUnitSquare.accepted 0)),
    verified (.unitPair (GenusTwoUnitPairs.StrictLinePoint.accepted 0 3).2),
    verified (.unitPair (GenusTwoUnitPairs.StrictLinePoint.accepted 0 1).2),
    verified (.mixed (BlowupTwoLinePointDivisors.value 0 true)),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 4 0 1).2),
    verified (.mixed (BlowupTwoLinePointDivisors.value 1 true)),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 4 1 1).2),
    verified (.mixed (BlowupTwoLinePointDivisors.value 2 true)),
    verified (.divisorPair (GenusTwoDivisorPairs.StrictLine.all_accepted 4 2 1).2),
    verified (.mixed BlowupTwoLinePointDivisors.primary),
    verified (.mixed (GenusTwoOneMarking.TwoBlowups.accepted 5)),
    verified (.mixed (GenusTwoOneMarking.TwoBlowups.accepted 6)),
    verified (.mixed (GenusTwoOneMarking.TwoBlowups.accepted 7)),
    verified (.mixed (GenusTwoOneMarking.TwoBlowups.accepted 8)),
    verified (.exceptionalPoint (q := requests 84) (v := 0) (by decide +kernel)),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 5 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 5 2).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 5 3).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 5 1).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 6 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 6 2).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 5 0 1).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 7 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 7 2).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 5 1 1).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 8 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 8 2).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 5 2 1).2),
    verified (.exceptionalPoint (q := requests 102) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 103) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 104) (v := 0) (by decide +kernel)),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 5 0 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 6 3).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 6 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 6 0 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 6 0 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 7 0 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 6 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 8 0 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 6 2 1).2),
    verified (.exceptionalPoint (q := requests 118) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 119) (v := 0) (by decide +kernel)),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 5 1 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 7 3).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 7 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 6 1 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 7 0 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 7 1 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 7 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 8 1 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 7 2 1).2),
    verified (.exceptionalPoint (q := requests 133) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 134) (v := 0) (by decide +kernel)),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 5 2 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 8 3).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 8 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 6 2 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 8 0 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 7 2 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 8 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 8 2 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 8 2 1).2),
    verified (.exceptionalPoint (q := requests 148) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 149) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 150) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 151) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 152) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 153) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 154) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 155) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 156) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 157) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 158) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 159) (v := 0) (by decide +kernel)),
    verified (.mixed (GenusTwoOneMarking.TwoBlowups.accepted 0)),
    verified (.mixed (GenusTwoOneMarking.TwoBlowups.accepted 1)),
    verified (.mixed (GenusTwoOneMarking.TwoBlowups.accepted 2)),
    verified (.mixed (GenusTwoOneMarking.TwoBlowups.accepted 3)),
    verified (.exceptionalPoint (q := requests 164) (v := 0) (by decide +kernel)),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 0 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 0 2).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 0 3).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 0 1).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 1 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 1 2).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 0 0 1).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 2 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 2 2).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 0 1 1).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 3 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 3 2).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 0 2 1).2),
    verified (.exceptionalPoint (q := requests 182) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 183) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 184) (v := 0) (by decide +kernel)),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 0 0 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 1 3).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 1 0 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 1 0 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 2 0 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 1 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 3 0 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 1 2 1).2),
    verified (.exceptionalPoint (q := requests 198) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 199) (v := 0) (by decide +kernel)),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 0 1 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 2 3).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 2 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 1 1 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 2 0 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 2 1 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 2 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 3 1 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 2 2 1).2),
    verified (.exceptionalPoint (q := requests 213) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 214) (v := 0) (by decide +kernel)),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 0 2 0).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 3 3).2),
    verified (.unitPair (GenusTwoUnitPairs.TwoBlowups.accepted 3 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 1 2 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 3 0 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 2 2 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 3 1 1).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 3 2 0).2),
    verified (.divisorPair (GenusTwoDivisorPairs.TwoBlowups.accepted 3 2 1).2),
    verified (.exceptionalPoint (q := requests 228) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 229) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 230) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 231) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 232) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 233) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 234) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 235) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 236) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 237) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 238) (v := 0) (by decide +kernel)),
    verified (.exceptionalPoint (q := requests 239) (v := 0) (by decide +kernel))] :
    Array (ProvenRow (X := .blowupTwo) 0))[i.val]'i.isLt

private theorem binding : ∀ i : Fin 192, (rows i).val =
    (requests (reductionIndex i), values (reductionIndex i)) := by decide +kernel

/-- Each selected ordinary specialization has an original geometric reconstruction route. -/
theorem reductions_accepted (i : Fin 192) :
    CheckedDescendant 0 (requests (reductionIndex i)) (values (reductionIndex i)) := by
  have h := (rows i).property
  rwa [binding i] at h

end TwoBlowups

end AxiomaticGW.GKM.GenusTwoEnergyOne
