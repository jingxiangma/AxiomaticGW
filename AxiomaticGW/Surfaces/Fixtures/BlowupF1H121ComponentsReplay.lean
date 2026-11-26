/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue00
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue01
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue02
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue03
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue04
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue05
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue06
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue07
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue08
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue09
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue10
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue11
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue12
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue13
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue14
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue15
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue16
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue17
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue18
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue19
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue20
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue21
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue22
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue23
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue24
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue25
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue26
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue27
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue28
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue29
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue30
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue31
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue32
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue33
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue34
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue35
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue36
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue37
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue38
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue39
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue40
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue41
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue42
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue43
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue44
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue45
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue46
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue47

/-!
# Existing residual cache from individually checked F1 components

Every candidate value remains untrusted until its explicit kernel check.
Component labels use sortCode: unit=0, H=1, E0=2, point=3.
Selector observation-log SHA256: d8b50f7e8ec84f6e3ace9671fdf99440d1c315d4b3e8499f60b57f75c88ddb60
Candidate input SHA256: 378c173898f3fc8df177d98bc64f66e7236b40c466df177f998602b0b0f79e7f
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.BlowupF1H121Components
open SurfaceGenusTwo
open BlowupF1CertifiedPoints (rational elliptic rational_eq elliptic_eq)

set_option maxHeartbeats 0 in
theorem keys_injective : Function.Injective key := by decide +kernel

theorem entries_eq (i : Fin 48) : entries i = residualTerms (key i) := by
  fin_cases i
  · exact entry_0_eq
  · exact entry_1_eq
  · exact entry_2_eq
  · exact entry_3_eq
  · exact entry_4_eq
  · exact entry_5_eq
  · exact entry_6_eq
  · exact entry_7_eq
  · exact entry_8_eq
  · exact entry_9_eq
  · exact entry_10_eq
  · exact entry_11_eq
  · exact entry_12_eq
  · exact entry_13_eq
  · exact entry_14_eq
  · exact entry_15_eq
  · exact entry_16_eq
  · exact entry_17_eq
  · exact entry_18_eq
  · exact entry_19_eq
  · exact entry_20_eq
  · exact entry_21_eq
  · exact entry_22_eq
  · exact entry_23_eq
  · exact entry_24_eq
  · exact entry_25_eq
  · exact entry_26_eq
  · exact entry_27_eq
  · exact entry_28_eq
  · exact entry_29_eq
  · exact entry_30_eq
  · exact entry_31_eq
  · exact entry_32_eq
  · exact entry_33_eq
  · exact entry_34_eq
  · exact entry_35_eq
  · exact entry_36_eq
  · exact entry_37_eq
  · exact entry_38_eq
  · exact entry_39_eq
  · exact entry_40_eq
  · exact entry_41_eq
  · exact entry_42_eq
  · exact entry_43_eq
  · exact entry_44_eq
  · exact entry_45_eq
  · exact entry_46_eq
  · exact entry_47_eq

def cache : ResidualCache .hirzebruchOne :=
  ResidualCache.ofEntries key entries keys_injective entries_eq

end AxiomaticGW.BlowupF1H121Components
