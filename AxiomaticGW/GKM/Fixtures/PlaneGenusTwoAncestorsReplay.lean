/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsLowPsi
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsPsiTwo
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsPsiThree
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsPsiFour
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsPsiFive
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsPsiSix

/-!
# Accepted shared ancestors for every plane few-marking request

Input SHA256: 640e00ec2d4b2055c49465d80a3590da42dec51772d34ea00bad356dad0950a8
Candidate values become certificates only after their full equations are checked.
The original canonical seeds and geometric hypotheses are unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoAncestors

open BelorousskiPandharipande SurfaceGenusTwo

private theorem row_0 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 0) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_pos (show (key 0).totalPsi ≤ 1 by decide +kernel), values_key]
  exact LowPsi.terminal_0

private theorem row_1 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 1) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_pos (show (key 1).totalPsi ≤ 1 by decide +kernel), values_key]
  exact LowPsi.terminal_1

private theorem row_2 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 2) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_pos (show (key 2).totalPsi ≤ 1 by decide +kernel), values_key]
  exact LowPsi.terminal_2

private theorem row_3 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 3) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_pos (show (key 3).totalPsi ≤ 1 by decide +kernel), values_key]
  exact LowPsi.terminal_3

private theorem row_4 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 4) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_pos (show (key 4).totalPsi ≤ 1 by decide +kernel), values_key]
  exact LowPsi.terminal_4

private theorem row_5 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 5) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_pos (show (key 5).totalPsi ≤ 1 by decide +kernel), values_key]
  exact LowPsi.terminal_5

private theorem row_6 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 6) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 6).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiTwo.reduction_6]
  decide +kernel

private theorem row_7 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 7) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 7).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiTwo.reduction_7]
  decide +kernel

private theorem row_8 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 8) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 8).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiTwo.reduction_8]
  decide +kernel

private theorem row_9 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 9) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 9).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiTwo.reduction_9]
  decide +kernel

private theorem row_10 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 10) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 10).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiTwo.reduction_10]
  decide +kernel

private theorem row_11 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 11) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 11).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiTwo.reduction_11]
  decide +kernel

private theorem row_12 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 12) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 12).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiThree.reduction_12]
  decide +kernel

private theorem row_13 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 13) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 13).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiThree.reduction_13]
  decide +kernel

private theorem row_14 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 14) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 14).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiThree.reduction_14]
  decide +kernel

private theorem row_15 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 15) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 15).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiThree.reduction_15]
  decide +kernel

private theorem row_16 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 16) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 16).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiThree.reduction_16]
  decide +kernel

private theorem row_17 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 17) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 17).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiThree.reduction_17]
  decide +kernel

private theorem row_18 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 18) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 18).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiThree.reduction_18]
  decide +kernel

private theorem row_19 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 19) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 19).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFour.reduction_19]
  decide +kernel

private theorem row_20 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 20) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 20).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFour.reduction_20]
  decide +kernel

private theorem row_21 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 21) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 21).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFour.reduction_21]
  decide +kernel

private theorem row_22 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 22) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 22).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFour.reduction_22]
  decide +kernel

private theorem row_23 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 23) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 23).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFour.reduction_23]
  decide +kernel

private theorem row_24 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 24) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 24).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFour.reduction_24]
  decide +kernel

private theorem row_25 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 25) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 25).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFour.reduction_25]
  decide +kernel

private theorem row_26 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 26) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 26).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFour.reduction_26]
  decide +kernel

private theorem row_27 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 27) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 27).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFour.reduction_27]
  decide +kernel

private theorem row_28 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 28) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 28).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFive.reduction_28]
  decide +kernel

private theorem row_29 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 29) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 29).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFive.reduction_29]
  decide +kernel

private theorem row_30 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 30) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 30).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFive.reduction_30]
  decide +kernel

private theorem row_31 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 31) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 31).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFive.reduction_31]
  decide +kernel

private theorem row_32 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 32) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 32).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFive.reduction_32]
  decide +kernel

private theorem row_33 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 33) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 33).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFive.reduction_33]
  decide +kernel

private theorem row_34 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 34) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 34).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiFive.reduction_34]
  decide +kernel

private theorem row_35 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 35) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 35).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiSix.reduction_35]
  decide +kernel

private theorem row_36 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 36) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 36).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiSix.reduction_36]
  decide +kernel

private theorem row_37 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 37) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 37).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiSix.reduction_37]
  decide +kernel

private theorem row_38 :
    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values (key 38) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 38).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiSix.reduction_38]
  decide +kernel

/-- All rows satisfy their original equations and include every dependency. -/
theorem accepted :
    checkAncestorValues (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values = true := by
  rw [checkAncestorValues, decide_eq_true_eq]
  intro q hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
  fin_cases i
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
  · exact row_9
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15
  · exact row_16
  · exact row_17
  · exact row_18
  · exact row_19
  · exact row_20
  · exact row_21
  · exact row_22
  · exact row_23
  · exact row_24
  · exact row_25
  · exact row_26
  · exact row_27
  · exact row_28
  · exact row_29
  · exact row_30
  · exact row_31
  · exact row_32
  · exact row_33
  · exact row_34
  · exact row_35
  · exact row_36
  · exact row_37
  · exact row_38

/-- Every cached row agrees with the existing terminating ancestor algorithm. -/
theorem values_eq (i : Fin 39) : value i =
    planeAncestorValueWith GenusTwoPlaneLine.values (key i) := by
  rw [← values_key]
  exact checkAncestorValues_sound _ queries values accepted (key i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The cache preserves every incoming full query, including queries outside it. -/
theorem query_eq (q : SurfaceQuery .plane) :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values q =
      planeQueryValueWith? GenusTwoPlaneLine.values q :=
  planeQueryValueCached?_eq_with _ queries values accepted q

end AxiomaticGW.GKM.PlaneGenusTwoAncestors
