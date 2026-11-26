/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Pilot
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootIndex0122
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1SelectedRootPilot0744

/-!
# Six exact numerical transfers from accepted original rows

These are consequences of existing original-row theorems and newly checked
outer relabellings with the original coefficient ratios. No sampled slot value
or component backend is used to establish a transfer.
-/

@[expose] public section

namespace AxiomaticGWTest.BlowupF1RootRelabelTransfersPilot

open AxiomaticGW BlowupF1RootAssembly BlowupF1RootRelabelTransfers.Pilot

/-- Transfer from the previously accepted original row 121. -/
theorem row140 : originalWeighted 140 = (3527 / 758160 : ℚ) := by
  rw [weighted140_eq121, originalWeighted121]
  norm_num

/-- Keep the second original occurrence instead of deduplicating the relation. -/
theorem row155 : originalWeighted 155 = (3527 / 758160 : ℚ) := by
  rw [weighted155_eq121, originalWeighted121]
  norm_num

/-- Reuse the exact accepted row-122 theorem. -/
theorem row141 : originalWeighted 141 = (3527 / 758160 : ℚ) := by
  rw [weighted141_eq122, BlowupF1FullRootReplay.Index0122.original_eq_claimed,
    BlowupF1FullRootReplay.Index0122.claimed]
  norm_num

/-- The second row-122 transport preserves its own relation coefficient. -/
theorem row156 : originalWeighted 156 = (3527 / 758160 : ℚ) := by
  rw [weighted156_eq122, BlowupF1FullRootReplay.Index0122.original_eq_claimed,
    BlowupF1FullRootReplay.Index0122.claimed]
  norm_num

/-- The accepted original row 744 has the same coefficient as row 762. -/
theorem row762 : originalWeighted 762 = (-227 / 224640 : ℚ) := by
  rw [weighted762_eq744, BlowupF1FullRootReplay.SelectedPilot0744.original_eq_claimed,
    BlowupF1FullRootReplay.SelectedPilot0744.claimed]
  norm_num

/-- Row 788 retains the exact two-thirds coefficient ratio. -/
theorem row788 : originalWeighted 788 = (-227 / 336960 : ℚ) := by
  rw [weighted788_eq744, BlowupF1FullRootReplay.SelectedPilot0744.original_eq_claimed,
    BlowupF1FullRootReplay.SelectedPilot0744.claimed]
  norm_num

end AxiomaticGWTest.BlowupF1RootRelabelTransfersPilot
