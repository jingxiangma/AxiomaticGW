/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch00
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0124SecondChecked
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0126
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0127
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0128
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0129
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0130

/-!
# Twelve further original F1 weighted-row values

Each consequence uses an existing structural relabelling equality and its signed
original coefficient ratio. The representative values come from accepted full
37-slot replays. Every occurrence remains a distinct original frame index.
-/

@[expose] public section
namespace AxiomaticGWTest.BlowupF1RootRelabelTransfersFirstEight
open AxiomaticGW BlowupF1RootAssembly BlowupF1RootRelabelTransfers.Batch00

/-- Exact original occurrence142, retaining its own relation coordinate. -/
theorem row142 : originalWeighted 142 = (-745 / 75816 : ℚ) := by
  rw [weighted142_eq124, BlowupF1FullRootReplay.Representative0124.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0124.claimed]
  norm_num

/-- Exact original occurrence157, retaining its own relation coordinate. -/
theorem row157 : originalWeighted 157 = (-745 / 75816 : ℚ) := by
  rw [weighted157_eq124, BlowupF1FullRootReplay.Representative0124.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0124.claimed]
  norm_num

/-- Exact original occurrence143, retaining its own relation coordinate. -/
theorem row143 : originalWeighted 143 = 0 := by
  rw [weighted143_eq126, BlowupF1FullRootReplay.Representative0126.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0126.claimed]
  norm_num

/-- Exact original occurrence158, retaining its own relation coordinate. -/
theorem row158 : originalWeighted 158 = 0 := by
  rw [weighted158_eq126, BlowupF1FullRootReplay.Representative0126.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0126.claimed]
  norm_num

/-- Exact original occurrence144, retaining its own relation coordinate. -/
theorem row144 : originalWeighted 144 = 0 := by
  rw [weighted144_eq127, BlowupF1FullRootReplay.Representative0127.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0127.claimed]
  norm_num

/-- Exact original occurrence159, retaining its own relation coordinate. -/
theorem row159 : originalWeighted 159 = 0 := by
  rw [weighted159_eq127, BlowupF1FullRootReplay.Representative0127.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0127.claimed]
  norm_num

/-- Exact original occurrence145, retaining its own relation coordinate. -/
theorem row145 : originalWeighted 145 = 0 := by
  rw [weighted145_eq128, BlowupF1FullRootReplay.Representative0128.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0128.claimed]
  norm_num

/-- Exact original occurrence160, retaining its own relation coordinate. -/
theorem row160 : originalWeighted 160 = 0 := by
  rw [weighted160_eq128, BlowupF1FullRootReplay.Representative0128.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0128.claimed]
  norm_num

/-- Exact original occurrence146, retaining its own relation coordinate. -/
theorem row146 : originalWeighted 146 = 0 := by
  rw [weighted146_eq129, BlowupF1FullRootReplay.Representative0129.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0129.claimed]
  norm_num

/-- Exact original occurrence161, retaining its own relation coordinate. -/
theorem row161 : originalWeighted 161 = 0 := by
  rw [weighted161_eq129, BlowupF1FullRootReplay.Representative0129.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0129.claimed]
  norm_num

/-- Exact original occurrence147, retaining its own relation coordinate. -/
theorem row147 : originalWeighted 147 = 0 := by
  rw [weighted147_eq130, BlowupF1FullRootReplay.Representative0130.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0130.claimed]
  norm_num

/-- Exact original occurrence162, retaining its own relation coordinate. -/
theorem row162 : originalWeighted 162 = 0 := by
  rw [weighted162_eq130, BlowupF1FullRootReplay.Representative0130.original_eq_claimed,
    BlowupF1FullRootReplay.Representative0130.claimed]
  norm_num

end AxiomaticGWTest.BlowupF1RootRelabelTransfersFirstEight
