module
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component315TRRBatch00
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component315TRRBatch01
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component315TRRBatch02
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component315TRRBatch03

@[expose] public section
set_option maxRecDepth 65536

namespace AxiomaticGW.Component315TRR
open BlowupF1CertifiedPoints (rational elliptic)

theorem all_parts_zero (i : Fin 31) : part i = 0 := by
  fin_cases i
  · exact part_0_eq_zero
  · exact part_1_eq_zero
  · exact part_2_eq_zero
  · exact part_3_eq_zero
  · exact part_4_eq_zero
  · exact part_5_eq_zero
  · exact part_6_eq_zero
  · exact part_7_eq_zero
  · exact part_8_eq_zero
  · exact part_9_eq_zero
  · exact part_10_eq_zero
  · exact part_11_eq_zero
  · exact part_12_eq_zero
  · exact part_13_eq_zero
  · exact part_14_eq_zero
  · exact part_15_eq_zero
  · exact part_16_eq_zero
  · exact part_17_eq_zero
  · exact part_18_eq_zero
  · exact part_19_eq_zero
  · exact part_20_eq_zero
  · exact part_21_eq_zero
  · exact part_22_eq_zero
  · exact part_23_eq_zero
  · exact part_24_eq_zero
  · exact part_25_eq_zero
  · exact part_26_eq_zero
  · exact part_27_eq_zero
  · exact part_28_eq_zero
  · exact part_29_eq_zero
  · exact part_30_eq_zero

theorem step_eq_zero :
    SurfaceGenusZero.ancestorStep (SurfaceLowGenusPointCache.rationalFuel X rational 0)
      q hg hp = 0 := by
  change (terms.map termValue).sum = 0
  apply List.sum_eq_zero
  intro z hz
  rcases List.mem_map.mp hz with ⟨t, ht, rfl⟩
  obtain ⟨i, rfl⟩ := List.get_of_mem ht
  exact all_parts_zero (Fin.cast terms_length i)

end AxiomaticGW.Component315TRR

namespace AxiomaticGW.BlowupF1CompleteHComponents
open BlowupF1CertifiedPoints (rational elliptic)
open Component315TRR (X q hg hp)

theorem component_315_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 315) = value 315 := by
  have hk : key 315 = q := by decide +kernel
  have hv : value 315 = 0 := by decide +kernel
  rw [hk, hv]
  change SurfaceLowGenusPointCache.componentValue X rational elliptic q = 0
  have hpsi : q.totalPsi = 1 := by decide +kernel
  rw [SurfaceLowGenusPointCache.componentValue, if_pos hg,
    SurfaceLowGenusPointCache.rationalValue, hpsi, SurfaceLowGenusPointCache.rationalFuel,
    dif_pos hg, dif_neg hp]
  exact Component315TRR.step_eq_zero

end AxiomaticGW.BlowupF1CompleteHComponents
