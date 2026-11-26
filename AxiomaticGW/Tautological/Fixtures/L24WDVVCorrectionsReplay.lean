/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24WDVV


/-!
# Exact incoming L24 correction coefficients

Input SHA256: 227cd365a71aa1377c2b6c79c5a15b3217edbaf348cab6bcc8f4ab2c543cebe7
All 71 contextual rows are compared to actual independently held Lean operations.
The initial BP coordinate claim is separate and requires its own graph replay.
-/

@[expose] public section

namespace AxiomaticGW.L24CorrectionsReplay
open RelationCertificate StrataOperation

set_option maxRecDepth 20000

/-- Incoming exact raw coordinates; validity is checked separately. -/
def wdvv0 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then 0 else (if i.val < 46
    then 0 else (if i.val < 48 then 0 else (if i.val < 49 then (-1 / 3) else 0)))))) else (if
    i.val < 75 then (if i.val < 62 then (if i.val < 56 then 0 else (if i.val < 59 then (if i.val
    < 57 then 0 else (if i.val < 58 then (1 / 6) else 0)) else (if i.val < 60 then (1 / 6) else
    0))) else (if i.val < 68 then (if i.val < 65 then (if i.val < 63 then 0 else (if i.val < 64
    then 0 else (1 / 6))) else (if i.val < 66 then 0 else (if i.val < 67 then (1 / 6) else 0)))
    else 0)) else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76
    then 0 else (if i.val < 77 then 0 else (-1 / 3))) else 0) else (if i.val < 84 then 0 else
    (if i.val < 86 then (if i.val < 85 then (-1 / 3) else 0) else 0))) else (if i.val < 94 then
    (if i.val < 91 then 0 else (if i.val < 92 then 0 else (if i.val < 93 then 0 else (1 / 6))))
    else (if i.val < 97 then (if i.val < 95 then 0 else (if i.val < 96 then (1 / 6) else 0))
    else 0))))) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem wdvv0_checked : L24WDVV.correctionCoordinates 0 = wdvv0 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def wdvv1 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then 0 else (if i.val < 46
    then 0 else (if i.val < 48 then 0 else (if i.val < 49 then 0 else (-1 / 3))))))) else (if
    i.val < 75 then (if i.val < 62 then (if i.val < 56 then 0 else (if i.val < 59 then (if i.val
    < 57 then 0 else (if i.val < 58 then 0 else (1 / 6))) else (if i.val < 60 then 0 else (if
    i.val < 61 then (1 / 6) else 0)))) else (if i.val < 68 then (if i.val < 65 then 0 else (if
    i.val < 66 then (1 / 6) else (if i.val < 67 then 0 else (1 / 6)))) else 0)) else (if i.val <
    88 then (if i.val < 81 then (if i.val < 78 then 0 else (if i.val < 79 then (-1 / 3) else 0))
    else (if i.val < 84 then 0 else (if i.val < 86 then (if i.val < 85 then 0 else (-1 / 3))
    else 0))) else (if i.val < 94 then 0 else (if i.val < 97 then (if i.val < 95 then (1 / 6)
    else (if i.val < 96 then 0 else (1 / 6))) else 0))))) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem wdvv1_checked : L24WDVV.correctionCoordinates 1 = wdvv1 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def wdvv2 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then 0 else (if i.val < 152
    then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else (if i.val < 110
    then (if i.val < 108 then (-1 / 3) else (if i.val < 109 then (1 / 3) else 0)) else (if i.val
    < 111 then 0 else (if i.val < 112 then (1 / 3) else 0)))) else (if i.val < 119 then (if
    i.val < 116 then (if i.val < 114 then 0 else (if i.val < 115 then (1 / 3) else (-1 / 3)))
    else (if i.val < 117 then 0 else (if i.val < 118 then (-1 / 3) else 0))) else 0)) else 0)
    else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem wdvv2_checked : L24WDVV.correctionCoordinates 2 = wdvv2 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def wdvv3 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then 0 else (if i.val < 152
    then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then 0
    else (if i.val < 105 then 0 else (if i.val < 106 then 0 else (-1 / 3)))) else (if i.val <
    110 then (if i.val < 108 then 0 else (if i.val < 109 then (1 / 3) else 0)) else (if i.val <
    111 then 0 else (if i.val < 112 then (1 / 3) else 0)))) else (if i.val < 119 then (if i.val
    < 116 then (if i.val < 114 then 0 else (if i.val < 115 then (1 / 3) else 0)) else (if i.val
    < 117 then (-1 / 3) else (if i.val < 118 then 0 else (-1 / 3)))) else 0)) else 0) else 0))
    else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem wdvv3_checked : L24WDVV.correctionCoordinates 3 = wdvv3 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def wdvv4 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then 0 else (if i.val < 152
    then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else (if i.val < 110
    then (if i.val < 108 then 0 else (if i.val < 109 then (1 / 3) else (-1 / 6))) else (if i.val
    < 111 then (-1 / 6) else (if i.val < 112 then (1 / 3) else (-1 / 6))))) else (if i.val < 119
    then (if i.val < 116 then (if i.val < 114 then (-1 / 6) else (if i.val < 115 then (1 / 3)
    else 0)) else 0) else (if i.val < 122 then (if i.val < 120 then (-1 / 6) else (if i.val <
    121 then (-1 / 6) else 0)) else 0))) else 0) else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem wdvv4_checked : L24WDVV.correctionCoordinates 4 = wdvv4 := by
  decide +kernel

/-- All checked incoming rows, in their retained source-operation order. -/
def wdvvRows : Fin 5 → Coordinates 815 :=
  ![wdvv0, wdvv1, wdvv2, wdvv3, wdvv4]

/-- Exact chosen rational weights; the final sum is checked below. -/
def wdvvWeights : Fin 5 → ℚ :=
  ![(10 / 3), -3, (-17 / 6), (-1 / 6), 1]

/-- Every row in this complete family has been replayed. -/
theorem wdvv_checked (i : Fin 5) :
    L24WDVV.correctionCoordinates i = wdvvRows i := by
  fin_cases i
  · exact wdvv0_checked
  · exact wdvv1_checked
  · exact wdvv2_checked
  · exact wdvv3_checked
  · exact wdvv4_checked

end AxiomaticGW.L24CorrectionsReplay
