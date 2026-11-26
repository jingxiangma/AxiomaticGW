module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block03

/-! Downstream use of private numerical providers through the interval adapter. -/

@[expose] public section
namespace AxiomaticGWTest.BlowupF1WeightedAssembly
open AxiomaticGW

theorem first_row : BlowupF1RootAssembly.originalWeighted 96 = 0 :=
  BlowupF1WeightedAssembly.checkedBlock03 0

theorem positive_row : BlowupF1RootAssembly.originalWeighted 121 = (1 / 2160 : ℚ) :=
  BlowupF1WeightedAssembly.checkedBlock03 25

theorem negative_row : BlowupF1RootAssembly.originalWeighted 124 = (-745 / 50544 : ℚ) :=
  BlowupF1WeightedAssembly.checkedBlock03 28

theorem last_row : BlowupF1RootAssembly.originalWeighted 127 = 0 :=
  BlowupF1WeightedAssembly.checkedBlock03 31

end AxiomaticGWTest.BlowupF1WeightedAssembly
