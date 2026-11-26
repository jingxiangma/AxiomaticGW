/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch00
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0131
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0132
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0134Replay

/-!
# Six original weighted rows from certified representatives131,132,134

Each proof retains its own original index and signed coefficient ratio, and
uses the exact structural relabelling theorem and full37-slot representative.
-/

@[expose] public section
namespace AxiomaticGWTest.BlowupF1RootRelabelTransfersRows131134
open AxiomaticGW BlowupF1RootAssembly BlowupF1RootRelabelTransfers.Batch00

theorem row148 : originalWeighted 148 = 0 := by
  rw [weighted148_eq131, BlowupF1FullRootReplay.Representative0131.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0131.claimed]
  norm_num

theorem row163 : originalWeighted 163 = 0 := by
  rw [weighted163_eq131, BlowupF1FullRootReplay.Representative0131.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0131.claimed]
  norm_num

theorem row149 : originalWeighted 149 = 0 := by
  rw [weighted149_eq132, BlowupF1FullRootReplay.Representative0132.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0132.claimed]
  norm_num

theorem row164 : originalWeighted 164 = 0 := by
  rw [weighted164_eq132, BlowupF1FullRootReplay.Representative0132.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0132.claimed]
  norm_num

theorem row150 : originalWeighted 150 = 0 := by
  rw [weighted150_eq134, BlowupF1FullRootReplay.Representative0134.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0134.claimed]
  norm_num

theorem row165 : originalWeighted 165 = 0 := by
  rw [weighted165_eq134, BlowupF1FullRootReplay.Representative0134.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0134.claimed]
  norm_num

end AxiomaticGWTest.BlowupF1RootRelabelTransfersRows131134
