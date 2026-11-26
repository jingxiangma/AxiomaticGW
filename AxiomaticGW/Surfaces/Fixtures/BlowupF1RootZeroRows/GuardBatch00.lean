/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly

/-!
# Original F1 rows killed by exact coordinates or the existing genus guard

Each original relation coordinate and required genus bound is checked against
the actual definitions. The statements concern the existing guarded contraction;
they do not assert vanishing of the unguarded contraction.
No sampled component value, native zero, or geometric premise is used.
-/

@[expose] public section
set_option Elab.async false

namespace AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00

open BlowupF1RootAssembly

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient51_nonzero : L24CorrectionsReplay.fullClaim 51 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard51 : 2 ≤ (L24Gluing.term 51).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted51 : originalWeighted 51 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 51 genusGuard51

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient52_nonzero : L24CorrectionsReplay.fullClaim 52 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard52 : 2 ≤ (L24Gluing.term 52).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted52 : originalWeighted 52 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 52 genusGuard52

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient56_nonzero : L24CorrectionsReplay.fullClaim 56 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard56 : 2 ≤ (L24Gluing.term 56).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted56 : originalWeighted 56 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 56 genusGuard56

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient57_nonzero : L24CorrectionsReplay.fullClaim 57 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard57 : 2 ≤ (L24Gluing.term 57).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted57 : originalWeighted 57 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 57 genusGuard57

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient59_nonzero : L24CorrectionsReplay.fullClaim 59 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard59 : 2 ≤ (L24Gluing.term 59).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted59 : originalWeighted 59 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 59 genusGuard59

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient62_nonzero : L24CorrectionsReplay.fullClaim 62 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard62 : 2 ≤ (L24Gluing.term 62).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted62 : originalWeighted 62 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 62 genusGuard62

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient63_nonzero : L24CorrectionsReplay.fullClaim 63 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard63 : 2 ≤ (L24Gluing.term 63).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted63 : originalWeighted 63 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 63 genusGuard63

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient64_nonzero : L24CorrectionsReplay.fullClaim 64 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard64 : 2 ≤ (L24Gluing.term 64).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted64 : originalWeighted 64 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 64 genusGuard64

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient66_nonzero : L24CorrectionsReplay.fullClaim 66 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard66 : 2 ≤ (L24Gluing.term 66).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted66 : originalWeighted 66 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 66 genusGuard66

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient69_nonzero : L24CorrectionsReplay.fullClaim 69 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard69 : 2 ≤ (L24Gluing.term 69).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted69 : originalWeighted 69 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 69 genusGuard69

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient70_nonzero : L24CorrectionsReplay.fullClaim 70 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard70 : 2 ≤ (L24Gluing.term 70).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted70 : originalWeighted 70 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 70 genusGuard70

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient74_nonzero : L24CorrectionsReplay.fullClaim 74 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard74 : 2 ≤ (L24Gluing.term 74).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted74 : originalWeighted 74 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 74 genusGuard74

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient76_nonzero : L24CorrectionsReplay.fullClaim 76 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard76 : 2 ≤ (L24Gluing.term 76).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted76 : originalWeighted 76 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 76 genusGuard76

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient81_nonzero : L24CorrectionsReplay.fullClaim 81 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard81 : 2 ≤ (L24Gluing.term 81).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted81 : originalWeighted 81 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 81 genusGuard81

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient83_nonzero : L24CorrectionsReplay.fullClaim 83 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard83 : 2 ≤ (L24Gluing.term 83).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted83 : originalWeighted 83 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 83 genusGuard83

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient88_nonzero : L24CorrectionsReplay.fullClaim 88 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard88 : 2 ≤ (L24Gluing.term 88).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted88 : originalWeighted 88 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 88 genusGuard88

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient93_nonzero : L24CorrectionsReplay.fullClaim 93 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard93 : 2 ≤ (L24Gluing.term 93).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted93 : originalWeighted 93 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 93 genusGuard93

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient95_nonzero : L24CorrectionsReplay.fullClaim 95 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard95 : 2 ≤ (L24Gluing.term 95).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted95 : originalWeighted 95 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 95 genusGuard95

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient97_nonzero : L24CorrectionsReplay.fullClaim 97 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard97 : 2 ≤ (L24Gluing.term 97).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted97 : originalWeighted 97 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 97 genusGuard97

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient101_nonzero : L24CorrectionsReplay.fullClaim 101 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard101 : 2 ≤ (L24Gluing.term 101).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted101 : originalWeighted 101 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 101 genusGuard101

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient105_nonzero : L24CorrectionsReplay.fullClaim 105 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard105 : 2 ≤ (L24Gluing.term 105).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted105 : originalWeighted 105 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 105 genusGuard105

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient109_nonzero : L24CorrectionsReplay.fullClaim 109 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard109 : 2 ≤ (L24Gluing.term 109).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted109 : originalWeighted 109 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 109 genusGuard109

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient110_nonzero : L24CorrectionsReplay.fullClaim 110 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard110 : 2 ≤ (L24Gluing.term 110).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted110 : originalWeighted 110 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 110 genusGuard110

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient112_nonzero : L24CorrectionsReplay.fullClaim 112 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard112 : 2 ≤ (L24Gluing.term 112).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted112 : originalWeighted 112 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 112 genusGuard112

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient113_nonzero : L24CorrectionsReplay.fullClaim 113 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard113 : 2 ≤ (L24Gluing.term 113).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted113 : originalWeighted 113 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 113 genusGuard113

end AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00
