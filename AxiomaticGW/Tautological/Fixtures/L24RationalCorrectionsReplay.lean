/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24RationalPsi


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
def rational0 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then 0 else (if i.val < 9 then 0 else (if
    i.val < 10 then 0 else (if i.val < 11 then 1 else 0)))) else 0) else (if i.val < 37 then 0
    else (if i.val < 43 then 0 else (if i.val < 46 then 0 else (if i.val < 48 then 0 else (if
    i.val < 49 then -1 else 0)))))) else 0) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational0_checked : L24RationalPsi.correctionCoordinates 0 = rational0 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational1 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then 0 else (if i.val < 9 then 0 else (if
    i.val < 10 then 0 else (if i.val < 11 then 0 else 1)))) else 0) else 0) else (if i.val < 75
    then (if i.val < 62 then (if i.val < 56 then 0 else (if i.val < 59 then (if i.val < 57 then
    0 else (if i.val < 58 then 0 else -1)) else 0)) else 0) else 0)) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational1_checked : L24RationalPsi.correctionCoordinates 1 = rational1 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational2 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then (if i.val < 15 then (if i.val
    < 13 then 1 else 0) else 0) else 0)) else 0) else (if i.val < 75 then (if i.val < 62 then 0
    else (if i.val < 68 then (if i.val < 65 then 0 else (if i.val < 66 then -1 else 0)) else 0))
    else 0)) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational2_checked : L24RationalPsi.correctionCoordinates 2 = rational2 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational3 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then 0 else (if i.val < 21 then 0
    else (if i.val < 23 then 0 else (if i.val < 24 then 1 else 0))))) else 0) else (if i.val <
    75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then -1
    else 0) else 0) else 0) else 0) else 0)) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational3_checked : L24RationalPsi.correctionCoordinates 3 = rational3 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational4 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then 0 else (if i.val < 21 then 0
    else (if i.val < 23 then 0 else (if i.val < 24 then 0 else 1))))) else 0) else (if i.val <
    75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 0
    else (if i.val < 52 then -1 else 0)) else 0) else 0) else 0) else 0)) else 0) else 0) else
    0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational4_checked : L24RationalPsi.correctionCoordinates 4 = rational4 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational5 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val
    < 26 then 1 else 0) else 0) else 0) else 0)) else (if i.val < 75 then 0 else (if i.val < 88
    then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then -1 else 0) else 0) else 0)
    else 0))) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational5_checked : L24RationalPsi.correctionCoordinates 5 = rational5 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational6 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val
    < 26 then 0 else (if i.val < 27 then 1 else 0)) else 0) else 0) else 0)) else (if i.val < 75
    then 0 else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then
    0 else (if i.val < 77 then -1 else 0)) else 0) else 0) else 0))) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational6_checked : L24RationalPsi.correctionCoordinates 6 = rational6 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational7 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val
    < 26 then 0 else (if i.val < 27 then 0 else 1)) else 0) else 0) else 0)) else (if i.val < 75
    then 0 else (if i.val < 88 then (if i.val < 81 then 0 else (if i.val < 84 then (if i.val <
    82 then 0 else (if i.val < 83 then -1 else 0)) else 0)) else 0))) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational7_checked : L24RationalPsi.correctionCoordinates 7 = rational7 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational8 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then (if i.val < 28 then 0 else
    (if i.val < 29 then 1 else 0)) else 0) else 0)) else (if i.val < 75 then 0 else (if i.val <
    88 then (if i.val < 81 then 0 else (if i.val < 84 then (if i.val < 82 then 0 else (if i.val
    < 83 then 0 else -1)) else 0)) else 0))) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational8_checked : L24RationalPsi.correctionCoordinates 8 = rational8 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational9 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then 0 else (if i.val < 34 then 0
    else (if i.val < 35 then 1 else 0))) else 0)) else (if i.val < 75 then (if i.val < 62 then
    (if i.val < 56 then 0 else (if i.val < 59 then 0 else (if i.val < 60 then 0 else (if i.val <
    61 then -1 else 0)))) else 0) else 0)) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational9_checked : L24RationalPsi.correctionCoordinates 9 = rational9 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational10 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then 0 else (if i.val < 34 then 0
    else (if i.val < 35 then 0 else (if i.val < 36 then 1 else 0)))) else 0)) else (if i.val <
    75 then 0 else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76
    then 0 else (if i.val < 77 then 0 else -1)) else 0) else 0) else 0))) else 0) else 0) else
    0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational10_checked : L24RationalPsi.correctionCoordinates 10 = rational10 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational11 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then 0 else (if i.val < 34 then 0
    else (if i.val < 35 then 0 else (if i.val < 36 then 0 else 1)))) else 0)) else (if i.val <
    75 then 0 else (if i.val < 88 then 0 else (if i.val < 94 then 0 else (if i.val < 97 then (if
    i.val < 95 then -1 else 0) else 0))))) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational11_checked : L24RationalPsi.correctionCoordinates 11 = rational11 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational12 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then (if i.val < 40 then
    (if i.val < 38 then 0 else (if i.val < 39 then 0 else 1)) else 0) else 0))) else (if i.val <
    75 then (if i.val < 62 then 0 else (if i.val < 68 then (if i.val < 65 then 0 else (if i.val
    < 66 then 0 else (if i.val < 67 then 0 else -1))) else 0)) else 0)) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational12_checked : L24RationalPsi.correctionCoordinates 12 = rational12 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational13 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then (if i.val < 40 then 0
    else (if i.val < 41 then 1 else 0)) else 0))) else (if i.val < 75 then 0 else (if i.val < 88
    then (if i.val < 81 then 0 else (if i.val < 84 then 0 else (if i.val < 86 then (if i.val <
    85 then -1 else 0) else 0))) else 0))) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational13_checked : L24RationalPsi.correctionCoordinates 13 = rational13 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational14 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then (if i.val < 40 then 0
    else (if i.val < 41 then 0 else (if i.val < 42 then 1 else 0))) else 0))) else (if i.val <
    75 then 0 else (if i.val < 88 then 0 else (if i.val < 94 then 0 else (if i.val < 97 then (if
    i.val < 95 then 0 else (if i.val < 96 then 0 else -1)) else 0))))) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational14_checked : L24RationalPsi.correctionCoordinates 14 = rational14 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational15 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then 0 else (if i.val < 46
    then (if i.val < 44 then 0 else (if i.val < 45 then 1 else 0)) else 0)))) else (if i.val <
    75 then (if i.val < 62 then 0 else (if i.val < 68 then 0 else (if i.val < 71 then (if i.val
    < 69 then 0 else (if i.val < 70 then 0 else -1)) else (if i.val < 73 then 0 else (if i.val <
    74 then 0 else -1))))) else (if i.val < 88 then (if i.val < 81 then 0 else (if i.val < 84
    then (if i.val < 82 then -1 else 0) else 0)) else 0))) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational15_checked : L24RationalPsi.correctionCoordinates 15 = rational15 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational16 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then 0 else (if i.val < 46
    then (if i.val < 44 then 0 else (if i.val < 45 then 0 else 1)) else 0)))) else (if i.val <
    75 then (if i.val < 62 then 0 else (if i.val < 68 then (if i.val < 65 then (if i.val < 63
    then 0 else (if i.val < 64 then -1 else 0)) else 0) else 0)) else (if i.val < 88 then 0 else
    (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then -1 else 0) else (if i.val < 92
    then 0 else (if i.val < 93 then -1 else 0))) else 0)))) else 0) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational16_checked : L24RationalPsi.correctionCoordinates 16 = rational16 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational17 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then 0 else (if i.val < 46
    then 0 else (if i.val < 48 then (if i.val < 47 then 1 else 0) else 0))))) else (if i.val <
    75 then (if i.val < 62 then (if i.val < 56 then 0 else (if i.val < 59 then (if i.val < 57
    then -1 else 0) else 0)) else 0) else (if i.val < 88 then 0 else (if i.val < 94 then 0 else
    (if i.val < 97 then 0 else (if i.val < 99 then (if i.val < 98 then -1 else 0) else 0))))))
    else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then (if
    i.val < 104 then (if i.val < 102 then -1 else 0) else 0) else 0) else 0) else 0) else 0))
    else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational17_checked : L24RationalPsi.correctionCoordinates 17 = rational17 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational18 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then 0 else (if i.val < 46
    then 0 else (if i.val < 48 then (if i.val < 47 then 0 else 1) else 0))))) else (if i.val <
    75 then (if i.val < 62 then (if i.val < 56 then 0 else (if i.val < 59 then (if i.val < 57
    then -1 else 0) else 0)) else 0) else (if i.val < 88 then 0 else (if i.val < 94 then 0 else
    (if i.val < 97 then 0 else (if i.val < 99 then (if i.val < 98 then -1 else 0) else 0))))))
    else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then (if
    i.val < 104 then 0 else (if i.val < 105 then 0 else (if i.val < 106 then -1 else 0))) else
    0) else 0) else 0) else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational18_checked : L24RationalPsi.correctionCoordinates 18 = rational18 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational19 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then 0 else
    (if i.val < 54 then 0 else (if i.val < 55 then 1 else 0))) else 0) else 0) else 0)) else (if
    i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then (if i.val <
    104 then 0 else (if i.val < 105 then 0 else (if i.val < 106 then 0 else -1))) else 0) else
    0) else 0) else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational19_checked : L24RationalPsi.correctionCoordinates 19 = rational19 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational20 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then 0 else
    (if i.val < 54 then 0 else (if i.val < 55 then 0 else 1))) else 0) else 0) else 0)) else (if
    i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else (if
    i.val < 110 then (if i.val < 108 then -1 else 0) else 0)) else 0) else 0) else 0)) else 0)
    else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational20_checked : L24RationalPsi.correctionCoordinates 20 = rational20 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational21 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then (if i.val < 62 then 0 else (if i.val < 68 then 0 else (if i.val <
    71 then 0 else (if i.val < 73 then (if i.val < 72 then 1 else 0) else 0)))) else 0)) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then (if
    i.val < 104 then 0 else (if i.val < 105 then 0 else (if i.val < 106 then 0 else -1))) else
    0) else 0) else 0) else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational21_checked : L24RationalPsi.correctionCoordinates 21 = rational21 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational22 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then (if i.val < 62 then 0 else (if i.val < 68 then 0 else (if i.val <
    71 then 0 else (if i.val < 73 then (if i.val < 72 then 0 else 1) else 0)))) else 0)) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else
    (if i.val < 110 then (if i.val < 108 then 0 else (if i.val < 109 then 0 else -1)) else 0))
    else 0) else 0) else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational22_checked : L24RationalPsi.correctionCoordinates 22 = rational22 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational23 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then (if i.val < 62 then 0 else (if i.val < 68 then 0 else (if i.val <
    71 then 0 else (if i.val < 73 then 0 else (if i.val < 74 then 1 else 0))))) else 0)) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else
    (if i.val < 110 then 0 else (if i.val < 111 then 0 else (if i.val < 112 then 0 else -1))))
    else 0) else 0) else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational23_checked : L24RationalPsi.correctionCoordinates 23 = rational23 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational24 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then 0 else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then
    0 else (if i.val < 79 then 0 else (if i.val < 80 then 1 else 0))) else 0) else 0))) else (if
    i.val < 152 then (if i.val < 126 then (if i.val < 113 then 0 else (if i.val < 119 then (if
    i.val < 116 then (if i.val < 114 then 0 else (if i.val < 115 then 0 else -1)) else 0) else
    0)) else 0) else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational24_checked : L24RationalPsi.correctionCoordinates 24 = rational24 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational25 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then 0 else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then
    0 else (if i.val < 79 then 0 else (if i.val < 80 then 0 else 1))) else 0) else 0))) else (if
    i.val < 152 then (if i.val < 126 then (if i.val < 113 then 0 else (if i.val < 119 then (if
    i.val < 116 then 0 else (if i.val < 117 then -1 else 0)) else 0)) else 0) else 0)) else 0)
    else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational25_checked : L24RationalPsi.correctionCoordinates 25 = rational25 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational26 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then 0 else (if i.val < 88 then (if i.val < 81 then 0 else (if i.val <
    84 then 0 else (if i.val < 86 then 0 else (if i.val < 87 then 1 else 0)))) else 0))) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then 0 else (if i.val < 119 then
    (if i.val < 116 then 0 else (if i.val < 117 then 0 else (if i.val < 118 then -1 else 0)))
    else 0)) else 0) else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational26_checked : L24RationalPsi.correctionCoordinates 26 = rational26 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational27 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then 0 else (if i.val < 88 then (if i.val < 81 then 0 else (if i.val <
    84 then 0 else (if i.val < 86 then 0 else (if i.val < 87 then 0 else 1)))) else 0))) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then 0 else (if i.val < 119 then
    (if i.val < 116 then 0 else (if i.val < 117 then 0 else (if i.val < 118 then 0 else -1)))
    else 0)) else 0) else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational27_checked : L24RationalPsi.correctionCoordinates 27 = rational27 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational28 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then 0 else (if i.val < 88 then 0 else (if i.val < 94 then (if i.val <
    91 then (if i.val < 89 then 0 else (if i.val < 90 then 1 else 0)) else 0) else 0)))) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else
    (if i.val < 110 then (if i.val < 108 then -1 else 0) else 0)) else 0) else 0) else 0)) else
    0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational28_checked : L24RationalPsi.correctionCoordinates 28 = rational28 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational29 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then 0 else (if i.val < 88 then 0 else (if i.val < 94 then (if i.val <
    91 then (if i.val < 89 then 0 else (if i.val < 90 then 0 else 1)) else 0) else 0)))) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then 0 else (if i.val < 119 then
    (if i.val < 116 then (if i.val < 114 then 0 else (if i.val < 115 then 0 else -1)) else 0)
    else 0)) else 0) else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational29_checked : L24RationalPsi.correctionCoordinates 29 = rational29 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational30 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then 0 else (if i.val < 88 then 0 else (if i.val < 94 then (if i.val <
    91 then 0 else (if i.val < 92 then 1 else 0)) else 0)))) else (if i.val < 152 then (if i.val
    < 126 then (if i.val < 113 then 0 else (if i.val < 119 then (if i.val < 116 then 0 else (if
    i.val < 117 then 0 else (if i.val < 118 then -1 else 0))) else 0)) else 0) else 0)) else 0)
    else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational30_checked : L24RationalPsi.correctionCoordinates 30 = rational30 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational31 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then 0 else (if i.val < 88 then 0 else (if i.val < 94 then 0 else (if
    i.val < 97 then 0 else (if i.val < 99 then (if i.val < 98 then 0 else 1) else 0)))))) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else
    (if i.val < 110 then 0 else (if i.val < 111 then -1 else 0))) else 0) else 0) else 0)) else
    0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational31_checked : L24RationalPsi.correctionCoordinates 31 = rational31 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational32 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then 0 else (if i.val < 88 then 0 else (if i.val < 94 then 0 else (if
    i.val < 97 then 0 else (if i.val < 99 then 0 else (if i.val < 100 then 1 else 0))))))) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then 0 else (if i.val < 119 then
    (if i.val < 116 then 0 else (if i.val < 117 then -1 else 0)) else 0)) else 0) else 0)) else
    0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational32_checked : L24RationalPsi.correctionCoordinates 32 = rational32 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational33 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then 0 else (if i.val < 88 then 0 else (if i.val < 94 then 0 else (if
    i.val < 97 then 0 else (if i.val < 99 then 0 else (if i.val < 100 then 0 else 1))))))) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then 0 else (if i.val < 119 then 0
    else (if i.val < 122 then (if i.val < 120 then -1 else 0) else 0))) else 0) else 0)) else 0)
    else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational33_checked : L24RationalPsi.correctionCoordinates 33 = rational33 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational34 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then 0 else (if i.val < 152
    then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then (if
    i.val < 102 then 0 else (if i.val < 103 then 1 else 0)) else 0) else 0) else (if i.val < 119
    then (if i.val < 116 then (if i.val < 114 then -1 else 0) else 0) else 0)) else 0) else 0))
    else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational34_checked : L24RationalPsi.correctionCoordinates 34 = rational34 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational35 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then 0 else (if i.val < 152
    then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then (if
    i.val < 102 then 0 else (if i.val < 103 then 0 else 1)) else 0) else 0) else (if i.val < 119
    then (if i.val < 116 then 0 else (if i.val < 117 then 0 else (if i.val < 118 then 0 else
    -1))) else 0)) else 0) else 0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational35_checked : L24RationalPsi.correctionCoordinates 35 = rational35 := by
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def rational36 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then 0 else (if i.val < 152
    then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then 0
    else (if i.val < 105 then 1 else 0)) else 0) else (if i.val < 119 then 0 else (if i.val <
    122 then (if i.val < 120 then 0 else (if i.val < 121 then -1 else 0)) else 0))) else 0) else
    0)) else 0) else 0)

/-- The full incoming row agrees with its actual contextual source image. -/
theorem rational36_checked : L24RationalPsi.correctionCoordinates 36 = rational36 := by
  decide +kernel

/-- All checked incoming rows, in their retained source-operation order. -/
def rationalRows : Fin 37 → Coordinates 815 :=
  ![rational0, rational1, rational2, rational3, rational4, rational5, rational6, rational7,
    rational8, rational9, rational10, rational11, rational12, rational13, rational14,
    rational15, rational16, rational17, rational18, rational19, rational20, rational21,
    rational22, rational23, rational24, rational25, rational26, rational27, rational28,
    rational29, rational30, rational31, rational32, rational33, rational34, rational35,
    rational36]

/-- Exact chosen rational weights; the final sum is checked below. -/
def rationalWeights : Fin 37 → ℚ :=
  ![-1, (-1 / 3), (-1 / 3), (-1 / 6), (1 / 6), (-1 / 6), (1 / 6), (-1 / 6), (1 / 6), (-1 / 3),
    -1, (-1 / 3), (-1 / 3), -1, (-1 / 3), (-1 / 3), -3, (-1 / 3), (-1 / 3), (-1 / 9), (1 / 3),
    (5 / 3), (1 / 3), (1 / 3), (1 / 3), (-1 / 9), (1 / 3), (-1 / 9), (1 / 9), (1 / 9), (1 / 9),
    (1 / 3), (5 / 3), (1 / 3), (1 / 3), (5 / 3), (1 / 3)]

/-- Every row in this complete family has been replayed. -/
theorem rational_checked (i : Fin 37) :
    L24RationalPsi.correctionCoordinates i = rationalRows i := by
  fin_cases i
  · exact rational0_checked
  · exact rational1_checked
  · exact rational2_checked
  · exact rational3_checked
  · exact rational4_checked
  · exact rational5_checked
  · exact rational6_checked
  · exact rational7_checked
  · exact rational8_checked
  · exact rational9_checked
  · exact rational10_checked
  · exact rational11_checked
  · exact rational12_checked
  · exact rational13_checked
  · exact rational14_checked
  · exact rational15_checked
  · exact rational16_checked
  · exact rational17_checked
  · exact rational18_checked
  · exact rational19_checked
  · exact rational20_checked
  · exact rational21_checked
  · exact rational22_checked
  · exact rational23_checked
  · exact rational24_checked
  · exact rational25_checked
  · exact rational26_checked
  · exact rational27_checked
  · exact rational28_checked
  · exact rational29_checked
  · exact rational30_checked
  · exact rational31_checked
  · exact rational32_checked
  · exact rational33_checked
  · exact rational34_checked
  · exact rational35_checked
  · exact rational36_checked

end AxiomaticGW.L24CorrectionsReplay
