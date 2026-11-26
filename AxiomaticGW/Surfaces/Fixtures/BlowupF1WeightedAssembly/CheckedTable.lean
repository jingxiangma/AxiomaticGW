/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block00
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block01
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block02
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block03
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block04
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block05
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block06
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block07
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block08
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block09
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block10
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block11
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block12
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block13
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block14
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block15
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block16
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block17
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block18
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block19
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block20
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block21
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block22
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block23
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block24
import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.Block25
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable

/-! # The complete original weighted F1 contraction

Every position is supplied by its bounded interval theorem. The finite append
partition only reassembles those original weighted values; it never evaluates
a component backend. The conclusion is the specified guarded L24 constant,
not an unconditional geometric GW invariant.
-/

@[expose] public section
set_option autoImplicit false
namespace AxiomaticGW.BlowupF1WeightedAssembly

open BlowupF1CandidateWeightedTable

/-- Match every original weighted row to the full candidate table. -/
theorem originalWeighted_eq_claimed (i : Fin 815) :
    BlowupF1RootAssembly.originalWeighted i = claimed i := by
  have h25 (j : Fin 15) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 800 j) = block25 j := by
    simpa only [Fin.castAdd_zero, Fin.cast_refl, id_eq] using checkedBlock25 j
  have h24 (j : Fin 47) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 768 j) =
        (Fin.append block24 (block25)) j := by
    refine Fin.addCases (m := 32) (n := 15) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock24 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 768 (Fin.natAdd 32 r) = Fin.natAdd 800 r := by
        apply Fin.ext
        change 768 + (32 + r.val) = 800 + r.val
        omega
      rw [hi]
      exact h25 r
  have h23 (j : Fin 79) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 736 j) =
        (Fin.append block23 (Fin.append block24 (block25))) j := by
    refine Fin.addCases (m := 32) (n := 47) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock23 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 736 (Fin.natAdd 32 r) = Fin.natAdd 768 r := by
        apply Fin.ext
        change 736 + (32 + r.val) = 768 + r.val
        omega
      rw [hi]
      exact h24 r
  have h22 (j : Fin 111) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 704 j) =
        (Fin.append block22 (Fin.append block23 (Fin.append block24 (block25)))) j := by
    refine Fin.addCases (m := 32) (n := 79) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock22 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 704 (Fin.natAdd 32 r) = Fin.natAdd 736 r := by
        apply Fin.ext
        change 704 + (32 + r.val) = 736 + r.val
        omega
      rw [hi]
      exact h23 r
  have h21 (j : Fin 143) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 672 j) =
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25))))) j := by
    refine Fin.addCases (m := 32) (n := 111) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock21 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 672 (Fin.natAdd 32 r) = Fin.natAdd 704 r := by
        apply Fin.ext
        change 672 + (32 + r.val) = 704 + r.val
        omega
      rw [hi]
      exact h22 r
  have h20 (j : Fin 175) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 640 j) =
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25)))))) j := by
    refine Fin.addCases (m := 32) (n := 143) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock20 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 640 (Fin.natAdd 32 r) = Fin.natAdd 672 r := by
        apply Fin.ext
        change 640 + (32 + r.val) = 672 + r.val
        omega
      rw [hi]
      exact h21 r
  have h19 (j : Fin 207) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 608 j) =
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25))))))) j := by
    refine Fin.addCases (m := 32) (n := 175) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock19 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 608 (Fin.natAdd 32 r) = Fin.natAdd 640 r := by
        apply Fin.ext
        change 608 + (32 + r.val) = 640 + r.val
        omega
      rw [hi]
      exact h20 r
  have h18 (j : Fin 239) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 576 j) =
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25)))))))) j := by
    refine Fin.addCases (m := 32) (n := 207) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock18 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 576 (Fin.natAdd 32 r) = Fin.natAdd 608 r := by
        apply Fin.ext
        change 576 + (32 + r.val) = 608 + r.val
        omega
      rw [hi]
      exact h19 r
  have h17 (j : Fin 271) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 544 j) =
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25))))))))) j := by
    refine Fin.addCases (m := 32) (n := 239) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock17 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 544 (Fin.natAdd 32 r) = Fin.natAdd 576 r := by
        apply Fin.ext
        change 544 + (32 + r.val) = 576 + r.val
        omega
      rw [hi]
      exact h18 r
  have h16 (j : Fin 303) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 512 j) =
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25)))))))))) j := by
    refine Fin.addCases (m := 32) (n := 271) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock16 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 512 (Fin.natAdd 32 r) = Fin.natAdd 544 r := by
        apply Fin.ext
        change 512 + (32 + r.val) = 544 + r.val
        omega
      rw [hi]
      exact h17 r
  have h15 (j : Fin 335) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 480 j) =
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 303) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock15 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 480 (Fin.natAdd 32 r) = Fin.natAdd 512 r := by
        apply Fin.ext
        change 480 + (32 + r.val) = 512 + r.val
        omega
      rw [hi]
      exact h16 r
  have h14 (j : Fin 367) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 448 j) =
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25)))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 335) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock14 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 448 (Fin.natAdd 32 r) = Fin.natAdd 480 r := by
        apply Fin.ext
        change 448 + (32 + r.val) = 480 + r.val
        omega
      rw [hi]
      exact h15 r
  have h13 (j : Fin 399) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 416 j) =
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 367) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock13 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 416 (Fin.natAdd 32 r) = Fin.natAdd 448 r := by
        apply Fin.ext
        change 416 + (32 + r.val) = 448 + r.val
        omega
      rw [hi]
      exact h14 r
  have h12 (j : Fin 431) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 384 j) =
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25)))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 399) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock12 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 384 (Fin.natAdd 32 r) = Fin.natAdd 416 r := by
        apply Fin.ext
        change 384 + (32 + r.val) = 416 + r.val
        omega
      rw [hi]
      exact h13 r
  have h11 (j : Fin 463) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 352 j) =
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 431) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock11 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 352 (Fin.natAdd 32 r) = Fin.natAdd 384 r := by
        apply Fin.ext
        change 352 + (32 + r.val) = 384 + r.val
        omega
      rw [hi]
      exact h12 r
  have h10 (j : Fin 495) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 320 j) =
          (Fin.append block10
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25)))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 463) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock10 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 320 (Fin.natAdd 32 r) = Fin.natAdd 352 r := by
        apply Fin.ext
        change 320 + (32 + r.val) = 352 + r.val
        omega
      rw [hi]
      exact h11 r
  have h09 (j : Fin 527) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 288 j) =
          (Fin.append block09
          (Fin.append block10
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25))))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 495) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock09 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 288 (Fin.natAdd 32 r) = Fin.natAdd 320 r := by
        apply Fin.ext
        change 288 + (32 + r.val) = 320 + r.val
        omega
      rw [hi]
      exact h10 r
  have h08 (j : Fin 559) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 256 j) =
          (Fin.append block08
          (Fin.append block09
          (Fin.append block10
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25)))))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 527) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock08 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 256 (Fin.natAdd 32 r) = Fin.natAdd 288 r := by
        apply Fin.ext
        change 256 + (32 + r.val) = 288 + r.val
        omega
      rw [hi]
      exact h09 r
  have h07 (j : Fin 591) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 224 j) =
          (Fin.append block07
          (Fin.append block08
          (Fin.append block09
          (Fin.append block10
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25))))))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 559) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock07 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 224 (Fin.natAdd 32 r) = Fin.natAdd 256 r := by
        apply Fin.ext
        change 224 + (32 + r.val) = 256 + r.val
        omega
      rw [hi]
      exact h08 r
  have h06 (j : Fin 623) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 192 j) =
          (Fin.append block06
          (Fin.append block07
          (Fin.append block08
          (Fin.append block09
          (Fin.append block10
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25)))))))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 591) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock06 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 192 (Fin.natAdd 32 r) = Fin.natAdd 224 r := by
        apply Fin.ext
        change 192 + (32 + r.val) = 224 + r.val
        omega
      rw [hi]
      exact h07 r
  have h05 (j : Fin 655) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 160 j) =
          (Fin.append block05
          (Fin.append block06
          (Fin.append block07
          (Fin.append block08
          (Fin.append block09
          (Fin.append block10
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25))))))))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 623) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock05 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 160 (Fin.natAdd 32 r) = Fin.natAdd 192 r := by
        apply Fin.ext
        change 160 + (32 + r.val) = 192 + r.val
        omega
      rw [hi]
      exact h06 r
  have h04 (j : Fin 687) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 128 j) =
          (Fin.append block04
          (Fin.append block05
          (Fin.append block06
          (Fin.append block07
          (Fin.append block08
          (Fin.append block09
          (Fin.append block10
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25)))))))))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 655) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock04 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 128 (Fin.natAdd 32 r) = Fin.natAdd 160 r := by
        apply Fin.ext
        change 128 + (32 + r.val) = 160 + r.val
        omega
      rw [hi]
      exact h05 r
  have h03 (j : Fin 719) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 96 j) =
          (Fin.append block03
          (Fin.append block04
          (Fin.append block05
          (Fin.append block06
          (Fin.append block07
          (Fin.append block08
          (Fin.append block09
          (Fin.append block10
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25))))))))))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 687) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock03 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 96 (Fin.natAdd 32 r) = Fin.natAdd 128 r := by
        apply Fin.ext
        change 96 + (32 + r.val) = 128 + r.val
        omega
      rw [hi]
      exact h04 r
  have h02 (j : Fin 751) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 64 j) =
          (Fin.append block02
          (Fin.append block03
          (Fin.append block04
          (Fin.append block05
          (Fin.append block06
          (Fin.append block07
          (Fin.append block08
          (Fin.append block09
          (Fin.append block10
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25)))))))))))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 719) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock02 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 64 (Fin.natAdd 32 r) = Fin.natAdd 96 r := by
        apply Fin.ext
        change 64 + (32 + r.val) = 96 + r.val
        omega
      rw [hi]
      exact h03 r
  have h01 (j : Fin 783) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 32 j) =
          (Fin.append block01
          (Fin.append block02
          (Fin.append block03
          (Fin.append block04
          (Fin.append block05
          (Fin.append block06
          (Fin.append block07
          (Fin.append block08
          (Fin.append block09
          (Fin.append block10
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25))))))))))))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 751) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock01 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 32 (Fin.natAdd 32 r) = Fin.natAdd 64 r := by
        apply Fin.ext
        change 32 + (32 + r.val) = 64 + r.val
        omega
      rw [hi]
      exact h02 r
  have h00 (j : Fin 815) :
      BlowupF1RootAssembly.originalWeighted (Fin.natAdd 0 j) =
          (Fin.append block00
          (Fin.append block01
          (Fin.append block02
          (Fin.append block03
          (Fin.append block04
          (Fin.append block05
          (Fin.append block06
          (Fin.append block07
          (Fin.append block08
          (Fin.append block09
          (Fin.append block10
          (Fin.append block11
          (Fin.append block12
          (Fin.append block13
          (Fin.append block14
          (Fin.append block15
          (Fin.append block16
          (Fin.append block17
          (Fin.append block18
          (Fin.append block19
          (Fin.append block20
          (Fin.append block21
          (Fin.append block22
          (Fin.append block23
          (Fin.append block24 (block25)))))))))))))))))))))))))) j := by
    refine Fin.addCases (m := 32) (n := 783) (fun l => ?_) (fun r => ?_) j
    · rw [Fin.append_left]
      exact checkedBlock00 l
    · rw [Fin.append_right]
      have hi : Fin.natAdd 0 (Fin.natAdd 32 r) = Fin.natAdd 32 r := by
        apply Fin.ext
        change 0 + (32 + r.val) = 32 + r.val
        omega
      rw [hi]
      exact h01 r
  simpa only [Fin.natAdd_zero, Fin.cast_refl, id_eq, claimed] using h00 i

/-- The fixed first F1 H constant from all 815 original weighted terms. -/
theorem pointConstantGuarded_eq :
    L24Relation.pointConstantGuarded BlowupF1RootAssembly.X 1
      BlowupF1RootAssembly.sourceCurve BlowupF1RootAssembly.insertions = (1 / 288 : ℚ) := by
  rw [BlowupF1RootAssembly.pointConstantGuarded_eq_sum_claims
    claimed originalWeighted_eq_claimed, claimed_sum]

end AxiomaticGW.BlowupF1WeightedAssembly
