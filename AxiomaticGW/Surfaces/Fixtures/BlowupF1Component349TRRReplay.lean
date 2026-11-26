module
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component349TRRBatch00
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component349TRRBatch01
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component349TRRBatch02
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Component349TRRBatch03

@[expose] public section
set_option maxRecDepth 65536

namespace AxiomaticGW.Component349TRR
open BlowupF1CertifiedPoints (rational elliptic)

theorem all_parts_checked (i : Fin 31) : part i = claimed i := by
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

theorem values_eq_claimed : terms.map termValue = List.ofFn claimed := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_ofFn, terms_length]
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_ofFn]
    exact all_parts_checked ⟨i, by simpa only [List.length_ofFn] using hi₂⟩

theorem step_computed :
    SurfaceGenusZero.ancestorStep (SurfaceLowGenusPointCache.rationalFuel X rational 0)
      q hg hp = 0 := by
  change (terms.map termValue).sum = 0
  rw [values_eq_claimed]
  decide +kernel

end AxiomaticGW.Component349TRR

namespace AxiomaticGW.BlowupF1CompleteHComponents
open BlowupF1CertifiedPoints (rational elliptic)
open Component349TRR (X q hg hp)

theorem component_349_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 349) = value 349 := by
  have hk : key 349 = q := by decide +kernel
  have hv : value 349 = 0 := by decide +kernel
  rw [hk, hv]
  change SurfaceLowGenusPointCache.componentValue X rational elliptic q = 0
  have hpsi : q.totalPsi = 1 := by decide +kernel
  rw [SurfaceLowGenusPointCache.componentValue, if_pos hg,
    SurfaceLowGenusPointCache.rationalValue, hpsi, SurfaceLowGenusPointCache.rationalFuel,
    dif_pos hg, dif_neg hp]
  exact Component349TRR.step_computed

end AxiomaticGW.BlowupF1CompleteHComponents
