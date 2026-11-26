module
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component670TRRBatch00
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component670TRRBatch01
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component670TRRBatch02
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component670TRRBatch03

@[expose] public section
set_option maxRecDepth 65536

namespace AxiomaticGW.Component670TRR
open BlowupF1CertifiedPoints (rational elliptic)

theorem all_parts_checked (i : Fin 32) : part i = claimed i := by
  fin_cases i
  · exact part_0_checked
  · exact part_1_checked
  · exact part_2_checked
  · exact part_3_checked
  · exact part_4_checked
  · exact part_5_checked
  · exact part_6_checked
  · exact part_7_checked
  · exact part_8_checked
  · exact part_9_checked
  · exact part_10_checked
  · exact part_11_checked
  · exact part_12_checked
  · exact part_13_checked
  · exact part_14_checked
  · exact part_15_checked
  · exact part_16_checked
  · exact part_17_checked
  · exact part_18_checked
  · exact part_19_checked
  · exact part_20_checked
  · exact part_21_checked
  · exact part_22_checked
  · exact part_23_checked
  · exact part_24_checked
  · exact part_25_checked
  · exact part_26_checked
  · exact part_27_checked
  · exact part_28_checked
  · exact part_29_checked
  · exact part_30_checked
  · exact part_31_checked

theorem values_eq_claimed : terms.map termValue = List.ofFn claimed := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_ofFn, terms_length]
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_ofFn]
    exact all_parts_checked ⟨i, by simpa only [List.length_ofFn] using hi₂⟩

theorem step_computed :
    SurfaceLowGenusPointCache.ellipticStep X rational
      (SurfaceLowGenusPointCache.ellipticFuel X rational elliptic 0) q hg hp = 0 := by
  change (terms.map termValue).sum = 0
  rw [values_eq_claimed]
  decide +kernel

end AxiomaticGW.Component670TRR

namespace AxiomaticGW.BlowupF1CompleteHComponents
open BlowupF1CertifiedPoints (rational elliptic)
open Component670TRR (X q hg hp)

theorem component_670_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 670) = value 670 := by
  have hk : key 670 = q := by decide +kernel
  have hv : value 670 = 0 := by decide +kernel
  rw [hk, hv]
  change SurfaceLowGenusPointCache.componentValue X rational elliptic q = 0
  have hpsi : q.totalPsi = 1 := by decide +kernel
  have hzero : ¬q.genus = 0 := by decide +kernel
  rw [SurfaceLowGenusPointCache.componentValue, if_neg hzero,
    SurfaceLowGenusPointCache.ellipticValue, hpsi, SurfaceLowGenusPointCache.ellipticFuel,
    dif_pos hg, dif_neg hp]
  exact Component670TRR.step_computed

end AxiomaticGW.BlowupF1CompleteHComponents
