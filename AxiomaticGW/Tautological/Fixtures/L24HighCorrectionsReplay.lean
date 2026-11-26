/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24HighPsi

public import AxiomaticGW.Tautological.StrataCoordinateRecords

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
def high0 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then
    1 else 0) else 0) else 0) else 0) else (if i.val < 37 then 0 else (if i.val < 43 then 0 else
    (if i.val < 46 then 0 else (if i.val < 48 then 0 else (if i.val < 49 then -1 else 0))))))
    else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if
    i.val < 51 then -1 else 0) else (if i.val < 54 then -3 else 0)) else (if i.val < 59 then (if
    i.val < 57 then -3 else 0) else 0)) else 0) else 0)) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then (if i.val < 107 then 0 else (if i.val < 110 then (if i.val <
    108 then 0 else (if i.val < 109 then 3 else 0)) else 0)) else (if i.val < 119 then 0 else
    (if i.val < 122 then (if i.val < 120 then 0 else (if i.val < 121 then 0 else (161 / 90)))
    else (if i.val < 124 then (if i.val < 123 then (161 / 90) else 0) else (if i.val < 125 then
    (-40 / 9) else 0))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129 then
    (if i.val < 127 then (206 / 51) else (161 / 90)) else (if i.val < 130 then (-40 / 9) else
    (if i.val < 131 then (407 / 180) else (-7 / 36)))) else (if i.val < 135 then (if i.val < 133
    then (407 / 180) else (if i.val < 134 then 0 else (-7 / 36))) else (if i.val < 137 then (if
    i.val < 136 then (407 / 180) else 0) else (if i.val < 138 then (-7 / 36) else (407 /
    180))))) else (if i.val < 145 then (if i.val < 142 then (if i.val < 140 then (-7 / 36) else
    0) else 0) else 0))) else 0)) else (if i.val < 305 then 0 else (if i.val < 356 then 0 else
    (if i.val < 381 then (if i.val < 368 then 0 else (if i.val < 374 then 0 else (if i.val < 377
    then 0 else (if i.val < 379 then (if i.val < 378 then (-161 / 90) else (-407 / 180)) else
    (if i.val < 380 then (-161 / 90) else (-407 / 180)))))) else (if i.val < 394 then (if i.val
    < 387 then (if i.val < 384 then (-25 / 9) else 0) else 0) else 0))))) else (if i.val < 611
    then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
    i.val < 413 then 0 else (if i.val < 416 then 0 else (if i.val < 417 then 0 else (if i.val <
    418 then (62 / 153) else (-19 / 90))))) else (if i.val < 425 then (if i.val < 422 then (-19
    / 90) else (if i.val < 423 then (-13 / 15) else (if i.val < 424 then (-13 / 30) else (-19 /
    90)))) else (if i.val < 428 then (if i.val < 426 then (-19 / 90) else (if i.val < 427 then
    (7 / 18) else 0)) else 0))) else 0) else (if i.val < 483 then 0 else (if i.val < 496 then
    (if i.val < 489 then 0 else (if i.val < 492 then (if i.val < 490 then (206 / 51) else 0)
    else 0)) else (if i.val < 502 then (if i.val < 499 then 0 else (if i.val < 500 then (-7 /
    36) else (67 / 720))) else 0)))) else 0) else (if i.val < 713 then (if i.val < 662 then 0
    else (if i.val < 687 then (if i.val < 674 then (if i.val < 668 then (if i.val < 665 then (if
    i.val < 663 then (-67 / 720) else (if i.val < 664 then (-67 / 720) else (-11 / 72))) else
    (if i.val < 666 then (-11 / 72) else (if i.val < 667 then (7 / 36) else (-1 / 40)))) else
    (if i.val < 671 then (-1 / 40) else (if i.val < 672 then (-37 / 90) else (if i.val < 673
    then (-37 / 90) else (473 / 12240))))) else (if i.val < 680 then (if i.val < 677 then (if
    i.val < 675 then (473 / 12240) else (-1 / 180)) else (if i.val < 678 then (-1 / 180) else
    (if i.val < 679 then (-1 / 180) else (-37 / 720)))) else (if i.val < 683 then (if i.val <
    681 then (-37 / 720) else 0) else 0))) else 0)) else (if i.val < 764 then 0 else (if i.val <
    789 then 0 else (if i.val < 802 then 0 else (if i.val < 808 then (if i.val < 805 then 0 else
    (if i.val < 806 then (-1 / 720) else 0)) else 0)))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high0Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (48, -1), (0, 0), (0, 0), (50, -1), (0, 0), (0, 0), (0, 0), (53, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (56, -3), (0, 0), (0, 0), (108, 3), (0, 0), (121, (161 /
    90)), (122, (161 / 90)), (0, 0), (124, (-40 / 9)), (0, 0), (0, 0), (0, 0), (126, (206 /
    51)), (127, (161 / 90)), (128, (161 / 90)), (129, (-40 / 9)), (0, 0), (0, 0), (130, (407 /
    180)), (131, (-7 / 36)), (132, (407 / 180)), (0, 0), (134, (-7 / 36)), (0, 0), (0, 0), (135,
    (407 / 180)), (0, 0), (137, (-7 / 36)), (138, (407 / 180)), (139, (-7 / 36)), (377, (-161 /
    90)), (378, (-407 / 180)), (379, (-161 / 90)), (380, (-407 / 180)), (381, (-25 / 9)), (382,
    (-25 / 9)), (383, (-25 / 9)), (417, (62 / 153)), (418, (-19 / 90)), (419, (-19 / 90)), (420,
    (-19 / 90)), (421, (-19 / 90)), (422, (-13 / 15)), (423, (-13 / 30)), (424, (-19 / 90)),
    (425, (-19 / 90)), (426, (7 / 18)), (0, 0), (489, (206 / 51)), (0, 0), (499, (-7 / 36)),
    (500, (67 / 720)), (501, (67 / 720)), (0, 0), (662, (-67 / 720)), (663, (-67 / 720)), (664,
    (-11 / 72)), (665, (-11 / 72)), (666, (7 / 36)), (667, (-1 / 40)), (668, (-1 / 40)), (669,
    (-1 / 40)), (670, (-1 / 40)), (671, (-37 / 90)), (672, (-37 / 90)), (673, (473 / 12240)),
    (674, (473 / 12240)), (675, (-1 / 180)), (676, (-1 / 180)), (677, (-1 / 180)), (678, (-1 /
    180)), (679, (-37 / 720)), (680, (-37 / 720)), (805, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high0Records_checked : imageRecords
    L24HighPsi.destination47 GenusTwoPsiPullbacksReplay.productThreeClaim = high0Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high0_checked : L24HighPsi.correctionCoordinates 0 = high0 := by
  change imageCoordinates L24HighPsi.destination47
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high0Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high1 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then
    0 else (if i.val < 2 then 1 else 0)) else 0) else 0) else 0) else (if i.val < 37 then 0 else
    (if i.val < 43 then 0 else (if i.val < 46 then 0 else (if i.val < 48 then 0 else (if i.val <
    49 then -1 else 0)))))) else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if
    i.val < 53 then (if i.val < 51 then 0 else (if i.val < 52 then -3 else -1)) else 0) else (if
    i.val < 59 then (if i.val < 57 then -3 else 0) else 0)) else 0) else 0)) else (if i.val <
    152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else (if i.val <
    110 then (if i.val < 108 then 3 else 0) else 0)) else (if i.val < 119 then 0 else (if i.val
    < 122 then (if i.val < 120 then 0 else (if i.val < 121 then 0 else (161 / 90))) else (if
    i.val < 124 then (if i.val < 123 then 0 else (161 / 90)) else (if i.val < 125 then (-40 / 9)
    else (407 / 180)))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129 then
    (if i.val < 127 then (-7 / 36) else (if i.val < 128 then (407 / 180) else 0)) else (if i.val
    < 130 then (-7 / 36) else (if i.val < 131 then 0 else (206 / 51)))) else (if i.val < 135
    then (if i.val < 133 then (161 / 90) else (if i.val < 134 then (161 / 90) else (-40 / 9)))
    else (if i.val < 137 then (if i.val < 136 then 0 else (407 / 180)) else (if i.val < 138 then
    (-7 / 36) else (407 / 180))))) else (if i.val < 145 then (if i.val < 142 then (if i.val <
    140 then (-7 / 36) else 0) else 0) else 0))) else 0)) else (if i.val < 305 then 0 else (if
    i.val < 356 then 0 else (if i.val < 381 then (if i.val < 368 then 0 else (if i.val < 374
    then 0 else (if i.val < 377 then 0 else (if i.val < 379 then (if i.val < 378 then (-161 /
    90) else (-407 / 180)) else (-25 / 9))))) else (if i.val < 394 then (if i.val < 387 then (if
    i.val < 384 then (if i.val < 382 then (-161 / 90) else (if i.val < 383 then (-407 / 180)
    else (-25 / 9))) else 0) else 0) else 0))))) else (if i.val < 611 then (if i.val < 509 then
    (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if i.val < 413 then 0 else
    (if i.val < 416 then 0 else (if i.val < 417 then 0 else (if i.val < 418 then (-19 / 90) else
    (62 / 153))))) else (if i.val < 425 then (if i.val < 422 then (if i.val < 420 then (-19 /
    90) else (if i.val < 421 then (-19 / 90) else (-13 / 15))) else (if i.val < 423 then (-19 /
    90) else (if i.val < 424 then (-13 / 30) else (7 / 18)))) else (if i.val < 428 then (if
    i.val < 426 then (-19 / 90) else (if i.val < 427 then (-19 / 90) else 0)) else 0))) else 0)
    else (if i.val < 483 then 0 else (if i.val < 496 then (if i.val < 489 then 0 else (if i.val
    < 492 then (if i.val < 490 then (206 / 51) else 0) else 0)) else (if i.val < 502 then (if
    i.val < 499 then 0 else (if i.val < 500 then (-7 / 36) else (if i.val < 501 then (67 / 720)
    else 0))) else (if i.val < 505 then (if i.val < 503 then (67 / 720) else 0) else 0))))) else
    0) else (if i.val < 713 then (if i.val < 662 then 0 else (if i.val < 687 then (if i.val <
    674 then (if i.val < 668 then (if i.val < 665 then (if i.val < 663 then (-67 / 720) else (if
    i.val < 664 then (-11 / 72) else (-67 / 720))) else (if i.val < 666 then (-11 / 72) else (if
    i.val < 667 then (-1 / 40) else (7 / 36)))) else (if i.val < 671 then (if i.val < 669 then
    (-1 / 40) else (if i.val < 670 then (-1 / 40) else (-37 / 90))) else (if i.val < 672 then
    (-1 / 40) else (if i.val < 673 then (-37 / 90) else (473 / 12240))))) else (if i.val < 680
    then (if i.val < 677 then (if i.val < 675 then (-1 / 180) else (if i.val < 676 then (473 /
    12240) else (-1 / 180))) else (if i.val < 678 then (-1 / 180) else (if i.val < 679 then (-37
    / 720) else (-1 / 180)))) else (if i.val < 683 then (if i.val < 681 then (-37 / 720) else 0)
    else 0))) else 0)) else (if i.val < 764 then 0 else (if i.val < 789 then 0 else (if i.val <
    802 then 0 else (if i.val < 808 then (if i.val < 805 then 0 else (if i.val < 806 then (-1 /
    720) else 0)) else 0)))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high1Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (1, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (48, -1), (0, 0), (0, 0), (52, -1), (0, 0), (0, 0), (0, 0), (51, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (56, -3), (0, 0), (0, 0), (107, 3), (0, 0), (121, (161 /
    90)), (123, (161 / 90)), (0, 0), (124, (-40 / 9)), (0, 0), (0, 0), (0, 0), (131, (206 /
    51)), (132, (161 / 90)), (133, (161 / 90)), (134, (-40 / 9)), (0, 0), (0, 0), (125, (407 /
    180)), (126, (-7 / 36)), (127, (407 / 180)), (0, 0), (129, (-7 / 36)), (0, 0), (0, 0), (136,
    (407 / 180)), (0, 0), (137, (-7 / 36)), (138, (407 / 180)), (139, (-7 / 36)), (377, (-161 /
    90)), (378, (-407 / 180)), (381, (-161 / 90)), (382, (-407 / 180)), (379, (-25 / 9)), (380,
    (-25 / 9)), (383, (-25 / 9)), (418, (62 / 153)), (417, (-19 / 90)), (419, (-19 / 90)), (420,
    (-19 / 90)), (422, (-19 / 90)), (421, (-13 / 15)), (423, (-13 / 30)), (426, (-19 / 90)),
    (425, (-19 / 90)), (424, (7 / 18)), (0, 0), (489, (206 / 51)), (0, 0), (499, (-7 / 36)),
    (500, (67 / 720)), (502, (67 / 720)), (0, 0), (662, (-67 / 720)), (664, (-67 / 720)), (663,
    (-11 / 72)), (665, (-11 / 72)), (667, (7 / 36)), (666, (-1 / 40)), (668, (-1 / 40)), (669,
    (-1 / 40)), (671, (-1 / 40)), (670, (-37 / 90)), (672, (-37 / 90)), (673, (473 / 12240)),
    (675, (473 / 12240)), (674, (-1 / 180)), (676, (-1 / 180)), (677, (-1 / 180)), (679, (-1 /
    180)), (678, (-37 / 720)), (680, (-37 / 720)), (805, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high1Records_checked : imageRecords
    L24HighPsi.destination48 GenusTwoPsiPullbacksReplay.productThreeClaim = high1Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high1_checked : L24HighPsi.correctionCoordinates 1 = high1 := by
  change imageCoordinates L24HighPsi.destination48
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high1Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high2 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then
    0 else (if i.val < 2 then 0 else 1)) else 0) else 0) else 0) else (if i.val < 37 then 0 else
    (if i.val < 43 then 0 else (if i.val < 46 then 0 else (if i.val < 48 then 0 else (if i.val <
    49 then 0 else -1)))))) else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if
    i.val < 53 then 0 else (if i.val < 54 then -1 else 0)) else (if i.val < 59 then (if i.val <
    57 then -1 else 0) else 0)) else 0) else 0)) else (if i.val < 152 then (if i.val < 126 then
    (if i.val < 113 then (if i.val < 107 then 0 else (if i.val < 110 then (if i.val < 108 then 0
    else (if i.val < 109 then 1 else 0)) else 0)) else (if i.val < 119 then 0 else (if i.val <
    122 then 0 else (if i.val < 124 then (if i.val < 123 then (-155 / 351) else 0) else (if
    i.val < 125 then (-70 / 351) else 0))))) else (if i.val < 139 then (if i.val < 132 then (if
    i.val < 129 then (if i.val < 127 then (328 / 1989) else (if i.val < 128 then 0 else (-155 /
    351))) else (if i.val < 130 then (-70 / 351) else (if i.val < 131 then (-155 / 351) else
    (-70 / 351)))) else (if i.val < 135 then (if i.val < 133 then 0 else (if i.val < 134 then 0
    else (328 / 1989))) else (if i.val < 137 then (if i.val < 136 then (-155 / 351) else 0) else
    (if i.val < 138 then (-70 / 351) else 0)))) else (if i.val < 145 then (if i.val < 142 then
    (if i.val < 140 then (328 / 1989) else 0) else 0) else 0))) else 0)) else (if i.val < 305
    then 0 else (if i.val < 356 then 0 else (if i.val < 381 then (if i.val < 368 then 0 else (if
    i.val < 374 then 0 else (if i.val < 377 then 0 else (if i.val < 379 then (155 / 351) else
    0)))) else (if i.val < 394 then (if i.val < 387 then (if i.val < 384 then (155 / 351) else
    0) else 0) else 0))))) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then
    (if i.val < 432 then (if i.val < 419 then (if i.val < 413 then 0 else (if i.val < 416 then 0
    else (if i.val < 417 then 0 else (if i.val < 418 then (206 / 5967) else (-23 / 195))))) else
    (if i.val < 425 then (if i.val < 422 then (if i.val < 420 then (-23 / 195) else (206 /
    5967)) else (if i.val < 423 then (-23 / 195) else (if i.val < 424 then (-23 / 390) else (-23
    / 195)))) else (if i.val < 428 then (if i.val < 426 then (206 / 5967) else (if i.val < 427
    then (206 / 5967) else 0)) else 0))) else 0) else (if i.val < 483 then 0 else (if i.val <
    496 then (if i.val < 489 then 0 else (if i.val < 492 then (if i.val < 490 then (328 / 1989)
    else 0) else 0)) else (if i.val < 502 then (if i.val < 499 then 0 else (if i.val < 500 then
    (-7 / 2808) else (if i.val < 501 then 0 else (-31 / 1404)))) else 0)))) else 0) else (if
    i.val < 713 then (if i.val < 662 then 0 else (if i.val < 687 then (if i.val < 674 then (if
    i.val < 668 then (if i.val < 665 then (if i.val < 663 then (31 / 1404) else (if i.val < 664
    then 0 else (31 / 1404))) else (if i.val < 666 then (31 / 1404) else (if i.val < 667 then (7
    / 2808) else (-749 / 14040)))) else (if i.val < 671 then (if i.val < 669 then (-749 / 14040)
    else (7 / 2808)) else (if i.val < 672 then (-749 / 14040) else (if i.val < 673 then (-749 /
    14040) else (-101 / 477360))))) else (if i.val < 680 then (if i.val < 677 then (if i.val <
    675 then (-101 / 477360) else (-3 / 1040)) else (if i.val < 678 then (-101 / 477360) else
    (if i.val < 679 then (-101 / 477360) else (-3 / 1040)))) else (if i.val < 683 then (if i.val
    < 681 then (-3 / 1040) else 0) else 0))) else 0)) else (if i.val < 764 then 0 else (if i.val
    < 789 then 0 else (if i.val < 802 then 0 else (if i.val < 808 then (if i.val < 805 then 0
    else (if i.val < 806 then (-1 / 56160) else 0)) else 0)))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high2Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (2, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (0, 0), (49, -1), (0, 0), (0, 0), (53, -1), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (56, -1), (0, 0), (0, 0), (108, 1), (0, 0), (122, (-155 / 351)),
    (0, 0), (0, 0), (124, (-70 / 351)), (0, 0), (0, 0), (0, 0), (126, (328 / 1989)), (128, (-155
    / 351)), (0, 0), (129, (-70 / 351)), (0, 0), (0, 0), (0, 0), (139, (328 / 1989)), (135,
    (-155 / 351)), (0, 0), (137, (-70 / 351)), (0, 0), (0, 0), (0, 0), (0, 0), (134, (328 /
    1989)), (130, (-155 / 351)), (131, (-70 / 351)), (0, 0), (0, 0), (377, (155 / 351)), (378,
    (155 / 351)), (381, (155 / 351)), (382, (155 / 351)), (383, (155 / 351)), (417, (206 /
    5967)), (420, (206 / 5967)), (421, (206 / 5967)), (418, (-23 / 195)), (419, (-23 / 195)),
    (422, (-23 / 195)), (423, (-23 / 390)), (425, (206 / 5967)), (424, (-23 / 195)), (426, (206
    / 5967)), (0, 0), (489, (328 / 1989)), (0, 0), (499, (-7 / 2808)), (501, (-31 / 1404)), (0,
    0), (0, 0), (0, 0), (662, (31 / 1404)), (664, (31 / 1404)), (665, (31 / 1404)), (666, (7 /
    2808)), (669, (7 / 2808)), (670, (7 / 2808)), (667, (-749 / 14040)), (668, (-749 / 14040)),
    (671, (-749 / 14040)), (672, (-749 / 14040)), (673, (-101 / 477360)), (674, (-101 /
    477360)), (677, (-101 / 477360)), (678, (-101 / 477360)), (675, (-3 / 1040)), (676, (-3 /
    1040)), (679, (-3 / 1040)), (680, (-3 / 1040)), (805, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high2Records_checked : imageRecords
    L24HighPsi.destination49 GenusTwoPsiPullbacksReplay.squareThreeClaim = high2Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high2_checked : L24HighPsi.correctionCoordinates 2 = high2 := by
  change imageCoordinates L24HighPsi.destination49
    GenusTwoPsiPullbacksReplay.squareThreeClaim = _
  rw [imageCoordinates_eq_records, high2Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high3 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then 0 else (if i.val <
    4 then 1 else 0)) else 0) else 0) else (if i.val < 37 then 0 else (if i.val < 43 then 0 else
    (if i.val < 46 then 0 else (if i.val < 48 then 0 else (if i.val < 49 then 0 else -3))))))
    else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if
    i.val < 51 then -1 else (if i.val < 52 then 0 else -1)) else 0) else (if i.val < 59 then (if
    i.val < 57 then -3 else 0) else 0)) else 0) else 0)) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then 0 else (if i.val <
    105 then 0 else (if i.val < 106 then 0 else 3))) else 0) else (if i.val < 119 then 0 else
    (if i.val < 122 then 0 else (if i.val < 124 then (161 / 90) else (if i.val < 125 then (-40 /
    9) else (407 / 180)))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129 then
    (if i.val < 127 then (-7 / 36) else (if i.val < 128 then 0 else (407 / 180))) else (if i.val
    < 130 then (-7 / 36) else (if i.val < 131 then (407 / 180) else (-7 / 36)))) else (if i.val
    < 135 then (if i.val < 133 then 0 else (if i.val < 134 then (407 / 180) else (-7 / 36)))
    else (if i.val < 137 then (161 / 90) else (if i.val < 138 then (-40 / 9) else 0)))) else (if
    i.val < 145 then (if i.val < 142 then (if i.val < 140 then (206 / 51) else 0) else 0) else
    0))) else 0)) else (if i.val < 305 then 0 else (if i.val < 356 then 0 else (if i.val < 381
    then (if i.val < 368 then 0 else (if i.val < 374 then 0 else (if i.val < 377 then 0 else (if
    i.val < 379 then (-25 / 9) else (if i.val < 380 then (-161 / 90) else (-407 / 180)))))) else
    (if i.val < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then (-161 /
    90) else (if i.val < 383 then (-407 / 180) else (-25 / 9))) else 0) else 0) else 0))))) else
    (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if
    i.val < 419 then (if i.val < 413 then 0 else (if i.val < 416 then 0 else (if i.val < 417
    then 0 else (-19 / 90)))) else (if i.val < 425 then (if i.val < 422 then (if i.val < 420
    then (-13 / 15) else (if i.val < 421 then (62 / 153) else (-19 / 90))) else (if i.val < 423
    then (-19 / 90) else (if i.val < 424 then (-13 / 30) else (-19 / 90)))) else (if i.val < 428
    then (if i.val < 426 then (7 / 18) else (if i.val < 427 then (-19 / 90) else 0)) else 0)))
    else 0) else (if i.val < 483 then 0 else (if i.val < 496 then (if i.val < 489 then 0 else
    (if i.val < 492 then (if i.val < 490 then (206 / 51) else 0) else 0)) else (if i.val < 502
    then (if i.val < 499 then 0 else (if i.val < 500 then (-7 / 36) else (if i.val < 501 then 0
    else (67 / 720)))) else (if i.val < 505 then (if i.val < 503 then (67 / 720) else 0) else
    0))))) else 0) else (if i.val < 713 then (if i.val < 662 then 0 else (if i.val < 687 then
    (if i.val < 674 then (if i.val < 668 then (if i.val < 665 then (if i.val < 663 then (-11 /
    72) else (-67 / 720)) else (if i.val < 666 then (-11 / 72) else (-1 / 40))) else (if i.val <
    671 then (if i.val < 669 then (-37 / 90) else (if i.val < 670 then (7 / 36) else (-1 / 40)))
    else (if i.val < 672 then (-1 / 40) else (if i.val < 673 then (-37 / 90) else (473 /
    12240))))) else (if i.val < 680 then (if i.val < 677 then (if i.val < 675 then (-1 / 180)
    else (if i.val < 676 then (-1 / 180) else (-37 / 720))) else (if i.val < 678 then (473 /
    12240) else (-1 / 180))) else (if i.val < 683 then (if i.val < 681 then (-37 / 720) else 0)
    else 0))) else 0)) else (if i.val < 764 then 0 else (if i.val < 789 then 0 else (if i.val <
    802 then 0 else (if i.val < 808 then (if i.val < 805 then 0 else (if i.val < 806 then (-1 /
    720) else 0)) else 0)))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high3Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (3, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (50, -1), (0, 0), (0, 0), (52, -1), (0, 0), (0, 0), (0, 0), (49, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (56, -3), (0, 0), (0, 0), (106, 3), (0, 0), (122, (161 /
    90)), (123, (161 / 90)), (0, 0), (124, (-40 / 9)), (0, 0), (0, 0), (0, 0), (139, (206 /
    51)), (135, (161 / 90)), (136, (161 / 90)), (137, (-40 / 9)), (0, 0), (0, 0), (125, (407 /
    180)), (126, (-7 / 36)), (128, (407 / 180)), (0, 0), (129, (-7 / 36)), (0, 0), (0, 0), (133,
    (407 / 180)), (0, 0), (134, (-7 / 36)), (130, (407 / 180)), (131, (-7 / 36)), (379, (-161 /
    90)), (380, (-407 / 180)), (381, (-161 / 90)), (382, (-407 / 180)), (377, (-25 / 9)), (378,
    (-25 / 9)), (383, (-25 / 9)), (420, (62 / 153)), (417, (-19 / 90)), (421, (-19 / 90)), (418,
    (-19 / 90)), (422, (-19 / 90)), (419, (-13 / 15)), (423, (-13 / 30)), (426, (-19 / 90)),
    (424, (-19 / 90)), (425, (7 / 18)), (0, 0), (489, (206 / 51)), (0, 0), (499, (-7 / 36)),
    (501, (67 / 720)), (502, (67 / 720)), (0, 0), (663, (-67 / 720)), (664, (-67 / 720)), (662,
    (-11 / 72)), (665, (-11 / 72)), (669, (7 / 36)), (666, (-1 / 40)), (670, (-1 / 40)), (667,
    (-1 / 40)), (671, (-1 / 40)), (668, (-37 / 90)), (672, (-37 / 90)), (673, (473 / 12240)),
    (677, (473 / 12240)), (674, (-1 / 180)), (678, (-1 / 180)), (675, (-1 / 180)), (679, (-1 /
    180)), (676, (-37 / 720)), (680, (-37 / 720)), (805, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high3Records_checked : imageRecords
    L24HighPsi.destination50 GenusTwoPsiPullbacksReplay.productThreeClaim = high3Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high3_checked : L24HighPsi.correctionCoordinates 3 = high3 := by
  change imageCoordinates L24HighPsi.destination50
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high3Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high4 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then 0 else (if i.val <
    4 then 0 else (if i.val < 5 then 1 else 0))) else 0) else 0) else 0) else (if i.val < 75
    then (if i.val < 62 then (if i.val < 56 then 0 else (if i.val < 59 then 0 else (if i.val <
    60 then 0 else (if i.val < 61 then -1 else 0)))) else (if i.val < 68 then (if i.val < 65
    then (if i.val < 63 then -1 else (if i.val < 64 then -1 else 0)) else 0) else 0)) else 0))
    else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0
    else (if i.val < 110 then 0 else (if i.val < 111 then 0 else (if i.val < 112 then 1 else
    0)))) else 0) else (if i.val < 139 then 0 else (if i.val < 145 then (if i.val < 142 then (if
    i.val < 140 then 0 else (if i.val < 141 then (-155 / 351) else 0)) else (if i.val < 143 then
    (-70 / 351) else (if i.val < 144 then (328 / 1989) else (-155 / 351)))) else (if i.val < 148
    then (if i.val < 146 then 0 else (if i.val < 147 then (-70 / 351) else 0)) else (if i.val <
    150 then (if i.val < 149 then (328 / 1989) else (-155 / 351)) else (if i.val < 151 then (-70
    / 351) else 0)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if
    i.val < 155 then (if i.val < 153 then (328 / 1989) else (if i.val < 154 then (-155 / 351)
    else (-70 / 351))) else 0) else 0) else 0) else 0))) else (if i.val < 305 then 0 else (if
    i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val < 394 then (if i.val < 387
    then (if i.val < 384 then 0 else (if i.val < 385 then 0 else (if i.val < 386 then 0 else
    (155 / 351)))) else (if i.val < 390 then (155 / 351) else (if i.val < 392 then (if i.val <
    391 then (155 / 351) else 0) else 0))) else 0))))) else (if i.val < 611 then (if i.val < 509
    then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then 0 else (if i.val < 425
    then 0 else (if i.val < 428 then (if i.val < 426 then 0 else (if i.val < 427 then 0 else
    (206 / 5967))) else (if i.val < 430 then (206 / 5967) else (-23 / 195))))) else (if i.val <
    445 then (if i.val < 438 then (if i.val < 435 then (if i.val < 433 then (-23 / 195) else (if
    i.val < 434 then (-23 / 390) else (206 / 5967))) else (if i.val < 436 then (-23 / 195) else
    (if i.val < 437 then (206 / 5967) else 0))) else 0) else 0)) else (if i.val < 483 then 0
    else (if i.val < 496 then (if i.val < 489 then 0 else (if i.val < 492 then (if i.val < 490
    then 0 else (if i.val < 491 then (328 / 1989) else 0)) else 0)) else (if i.val < 502 then 0
    else (if i.val < 505 then (if i.val < 503 then 0 else (if i.val < 504 then (-7 / 2808) else
    (-31 / 1404))) else 0))))) else 0) else (if i.val < 713 then (if i.val < 662 then 0 else (if
    i.val < 687 then (if i.val < 674 then 0 else (if i.val < 680 then 0 else (if i.val < 683
    then (if i.val < 681 then 0 else (if i.val < 682 then 0 else (31 / 1404))) else (if i.val <
    685 then (31 / 1404) else (7 / 2808))))) else (if i.val < 700 then (if i.val < 693 then (if
    i.val < 690 then (if i.val < 688 then (7 / 2808) else (-749 / 14040)) else (if i.val < 691
    then (-749 / 14040) else (if i.val < 692 then (-749 / 14040) else (-101 / 477360)))) else
    (if i.val < 696 then (-101 / 477360) else (-3 / 1040))) else 0))) else (if i.val < 764 then
    0 else (if i.val < 789 then 0 else (if i.val < 802 then 0 else (if i.val < 808 then (if
    i.val < 805 then 0 else (if i.val < 806 then 0 else (if i.val < 807 then (-1 / 56160) else
    0))) else 0)))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high4Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (4, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (0, 0), (60, -1), (0, 0), (0, 0), (62, -1), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (63, -1), (0, 0), (0, 0), (111, 1), (0, 0), (140, (-155 / 351)),
    (0, 0), (0, 0), (142, (-70 / 351)), (0, 0), (0, 0), (0, 0), (143, (328 / 1989)), (144, (-155
    / 351)), (0, 0), (146, (-70 / 351)), (0, 0), (0, 0), (0, 0), (148, (328 / 1989)), (149,
    (-155 / 351)), (0, 0), (150, (-70 / 351)), (0, 0), (0, 0), (0, 0), (0, 0), (152, (328 /
    1989)), (153, (-155 / 351)), (154, (-70 / 351)), (0, 0), (0, 0), (386, (155 / 351)), (387,
    (155 / 351)), (388, (155 / 351)), (389, (155 / 351)), (390, (155 / 351)), (427, (206 /
    5967)), (428, (206 / 5967)), (429, (206 / 5967)), (430, (-23 / 195)), (431, (-23 / 195)),
    (432, (-23 / 195)), (433, (-23 / 390)), (434, (206 / 5967)), (435, (-23 / 195)), (436, (206
    / 5967)), (0, 0), (490, (328 / 1989)), (0, 0), (503, (-7 / 2808)), (504, (-31 / 1404)), (0,
    0), (0, 0), (0, 0), (682, (31 / 1404)), (683, (31 / 1404)), (684, (31 / 1404)), (685, (7 /
    2808)), (686, (7 / 2808)), (687, (7 / 2808)), (688, (-749 / 14040)), (689, (-749 / 14040)),
    (690, (-749 / 14040)), (691, (-749 / 14040)), (692, (-101 / 477360)), (693, (-101 /
    477360)), (694, (-101 / 477360)), (695, (-101 / 477360)), (696, (-3 / 1040)), (697, (-3 /
    1040)), (698, (-3 / 1040)), (699, (-3 / 1040)), (806, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high4Records_checked : imageRecords
    L24HighPsi.destination57 GenusTwoPsiPullbacksReplay.squareThreeClaim = high4Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high4_checked : L24HighPsi.correctionCoordinates 4 = high4 := by
  change imageCoordinates L24HighPsi.destination57
    GenusTwoPsiPullbacksReplay.squareThreeClaim = _
  rw [imageCoordinates_eq_records, high4Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high5 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then 0 else (if i.val <
    4 then 0 else (if i.val < 5 then 0 else 1))) else 0) else 0) else 0) else (if i.val < 75
    then (if i.val < 62 then (if i.val < 56 then 0 else (if i.val < 59 then (if i.val < 57 then
    0 else (if i.val < 58 then -1 else 0)) else (if i.val < 60 then -1 else 0))) else (if i.val
    < 68 then (if i.val < 65 then (if i.val < 63 then -3 else (if i.val < 64 then -3 else 0))
    else 0) else 0)) else 0)) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113
    then (if i.val < 107 then 0 else (if i.val < 110 then 0 else (if i.val < 111 then 0 else (if
    i.val < 112 then 3 else 0)))) else 0) else (if i.val < 139 then 0 else (if i.val < 145 then
    (if i.val < 142 then (if i.val < 140 then 0 else (161 / 90)) else (if i.val < 143 then (-40
    / 9) else (if i.val < 144 then (206 / 51) else (161 / 90)))) else (if i.val < 148 then (if
    i.val < 146 then (161 / 90) else (if i.val < 147 then (-40 / 9) else (407 / 180))) else (if
    i.val < 150 then (if i.val < 149 then (-7 / 36) else (407 / 180)) else (if i.val < 151 then
    (-7 / 36) else (407 / 180))))))) else (if i.val < 177 then (if i.val < 164 then (if i.val <
    158 then (if i.val < 155 then (if i.val < 153 then (-7 / 36) else (if i.val < 154 then (407
    / 180) else (-7 / 36))) else 0) else 0) else 0) else 0))) else (if i.val < 305 then 0 else
    (if i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val < 394 then (if i.val < 387
    then (if i.val < 384 then 0 else (if i.val < 385 then (-161 / 90) else (if i.val < 386 then
    (-407 / 180) else (-161 / 90)))) else (if i.val < 390 then (if i.val < 388 then (-407 / 180)
    else (-25 / 9)) else (if i.val < 392 then (if i.val < 391 then (-25 / 9) else 0) else 0)))
    else 0))))) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val <
    432 then (if i.val < 419 then 0 else (if i.val < 425 then 0 else (if i.val < 428 then (if
    i.val < 426 then 0 else (if i.val < 427 then 0 else (62 / 153))) else (-19 / 90)))) else (if
    i.val < 445 then (if i.val < 438 then (if i.val < 435 then (if i.val < 433 then (-13 / 15)
    else (if i.val < 434 then (-13 / 30) else (-19 / 90))) else (if i.val < 436 then (-19 / 90)
    else (if i.val < 437 then (7 / 18) else 0))) else 0) else 0)) else (if i.val < 483 then 0
    else (if i.val < 496 then (if i.val < 489 then 0 else (if i.val < 492 then (if i.val < 490
    then 0 else (if i.val < 491 then (206 / 51) else 0)) else 0)) else (if i.val < 502 then 0
    else (if i.val < 505 then (if i.val < 503 then 0 else (if i.val < 504 then (-7 / 36) else
    (67 / 720))) else (if i.val < 507 then (if i.val < 506 then (67 / 720) else 0) else 0))))))
    else 0) else (if i.val < 713 then (if i.val < 662 then 0 else (if i.val < 687 then (if i.val
    < 674 then 0 else (if i.val < 680 then 0 else (if i.val < 683 then (if i.val < 681 then 0
    else (-67 / 720)) else (if i.val < 685 then (-11 / 72) else (if i.val < 686 then (7 / 36)
    else (-1 / 40)))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (-1
    / 40) else (if i.val < 691 then (-37 / 90) else (if i.val < 692 then (-37 / 90) else (473 /
    12240)))) else (if i.val < 696 then (if i.val < 694 then (473 / 12240) else (-1 / 180)) else
    (if i.val < 698 then (-1 / 180) else (-37 / 720)))) else 0))) else (if i.val < 764 then 0
    else (if i.val < 789 then 0 else (if i.val < 802 then 0 else (if i.val < 808 then (if i.val
    < 805 then 0 else (if i.val < 806 then 0 else (if i.val < 807 then (-1 / 720) else 0))) else
    0)))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high5Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (5, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (57, -1), (0, 0), (0, 0), (59, -1), (0, 0), (0, 0), (0, 0), (62, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (63, -3), (0, 0), (0, 0), (111, 3), (0, 0), (140, (161 /
    90)), (141, (161 / 90)), (0, 0), (142, (-40 / 9)), (0, 0), (0, 0), (0, 0), (143, (206 /
    51)), (144, (161 / 90)), (145, (161 / 90)), (146, (-40 / 9)), (0, 0), (0, 0), (147, (407 /
    180)), (148, (-7 / 36)), (149, (407 / 180)), (0, 0), (150, (-7 / 36)), (0, 0), (0, 0), (151,
    (407 / 180)), (0, 0), (152, (-7 / 36)), (153, (407 / 180)), (154, (-7 / 36)), (384, (-161 /
    90)), (385, (-407 / 180)), (386, (-161 / 90)), (387, (-407 / 180)), (388, (-25 / 9)), (389,
    (-25 / 9)), (390, (-25 / 9)), (427, (62 / 153)), (428, (-19 / 90)), (429, (-19 / 90)), (430,
    (-19 / 90)), (431, (-19 / 90)), (432, (-13 / 15)), (433, (-13 / 30)), (434, (-19 / 90)),
    (435, (-19 / 90)), (436, (7 / 18)), (0, 0), (490, (206 / 51)), (0, 0), (503, (-7 / 36)),
    (504, (67 / 720)), (505, (67 / 720)), (0, 0), (681, (-67 / 720)), (682, (-67 / 720)), (683,
    (-11 / 72)), (684, (-11 / 72)), (685, (7 / 36)), (686, (-1 / 40)), (687, (-1 / 40)), (688,
    (-1 / 40)), (689, (-1 / 40)), (690, (-37 / 90)), (691, (-37 / 90)), (692, (473 / 12240)),
    (693, (473 / 12240)), (694, (-1 / 180)), (695, (-1 / 180)), (696, (-1 / 180)), (697, (-1 /
    180)), (698, (-37 / 720)), (699, (-37 / 720)), (806, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high5Records_checked : imageRecords
    L24HighPsi.destination58 GenusTwoPsiPullbacksReplay.productThreeClaim = high5Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high5_checked : L24HighPsi.correctionCoordinates 5 = high5 := by
  change imageCoordinates L24HighPsi.destination58
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high5Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high6 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then 0 else (if i.val < 9 then (if i.val <
    7 then 1 else 0) else 0)) else 0) else 0) else (if i.val < 75 then (if i.val < 62 then (if
    i.val < 56 then 0 else (if i.val < 59 then (if i.val < 57 then 0 else (if i.val < 58 then 0
    else -1)) else 0)) else (if i.val < 68 then (if i.val < 65 then (if i.val < 63 then -1 else
    (if i.val < 64 then -1 else 0)) else 0) else 0)) else 0)) else (if i.val < 152 then (if
    i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else (if i.val < 110 then 0
    else (if i.val < 111 then 0 else (if i.val < 112 then 1 else 0)))) else 0) else (if i.val <
    139 then 0 else (if i.val < 145 then (if i.val < 142 then (if i.val < 140 then 0 else (if
    i.val < 141 then 0 else (-155 / 351))) else (if i.val < 143 then (-70 / 351) else (if i.val
    < 144 then (328 / 1989) else 0))) else (if i.val < 148 then (if i.val < 146 then (-155 /
    351) else (if i.val < 147 then (-70 / 351) else (-155 / 351))) else (if i.val < 150 then (if
    i.val < 149 then (-70 / 351) else 0) else (if i.val < 151 then (328 / 1989) else (-155 /
    351))))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
    155 then (if i.val < 153 then (-70 / 351) else (if i.val < 154 then 0 else (328 / 1989)))
    else 0) else 0) else 0) else 0))) else (if i.val < 305 then 0 else (if i.val < 356 then 0
    else (if i.val < 381 then 0 else (if i.val < 394 then (if i.val < 387 then (if i.val < 384
    then 0 else (if i.val < 385 then (155 / 351) else (if i.val < 386 then (155 / 351) else 0)))
    else (if i.val < 390 then (if i.val < 388 then 0 else (155 / 351)) else (if i.val < 392 then
    (if i.val < 391 then (155 / 351) else 0) else 0))) else 0))))) else (if i.val < 611 then (if
    i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then 0 else (if
    i.val < 425 then 0 else (if i.val < 428 then (if i.val < 426 then 0 else (if i.val < 427
    then 0 else (206 / 5967))) else (if i.val < 430 then (-23 / 195) else (206 / 5967))))) else
    (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then (if i.val < 433 then (-23 /
    195) else (if i.val < 434 then (-23 / 390) else (-23 / 195))) else (if i.val < 436 then (206
    / 5967) else (if i.val < 437 then (206 / 5967) else 0))) else 0) else 0)) else (if i.val <
    483 then 0 else (if i.val < 496 then (if i.val < 489 then 0 else (if i.val < 492 then (if
    i.val < 490 then 0 else (if i.val < 491 then (328 / 1989) else 0)) else 0)) else (if i.val <
    502 then 0 else (if i.val < 505 then (if i.val < 503 then 0 else (if i.val < 504 then (-7 /
    2808) else 0)) else (if i.val < 507 then (if i.val < 506 then (-31 / 1404) else 0) else
    0)))))) else 0) else (if i.val < 713 then (if i.val < 662 then 0 else (if i.val < 687 then
    (if i.val < 674 then 0 else (if i.val < 680 then 0 else (if i.val < 683 then (if i.val < 681
    then 0 else (if i.val < 682 then (31 / 1404) else 0)) else (if i.val < 685 then (31 / 1404)
    else (if i.val < 686 then (7 / 2808) else (-749 / 14040)))))) else (if i.val < 700 then (if
    i.val < 693 then (if i.val < 690 then (if i.val < 688 then (-749 / 14040) else (7 / 2808))
    else (if i.val < 691 then (-749 / 14040) else (if i.val < 692 then (-749 / 14040) else (-101
    / 477360)))) else (if i.val < 696 then (if i.val < 694 then (-101 / 477360) else (-3 /
    1040)) else (if i.val < 698 then (-101 / 477360) else (-3 / 1040)))) else 0))) else (if
    i.val < 764 then 0 else (if i.val < 789 then 0 else (if i.val < 802 then 0 else (if i.val <
    808 then (if i.val < 805 then 0 else (if i.val < 806 then 0 else (if i.val < 807 then (-1 /
    56160) else 0))) else 0)))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high6Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (6, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (0, 0), (58, -1), (0, 0), (0, 0), (62, -1), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (63, -1), (0, 0), (0, 0), (111, 1), (0, 0), (141, (-155 / 351)),
    (0, 0), (0, 0), (142, (-70 / 351)), (0, 0), (0, 0), (0, 0), (143, (328 / 1989)), (145, (-155
    / 351)), (0, 0), (146, (-70 / 351)), (0, 0), (0, 0), (0, 0), (154, (328 / 1989)), (151,
    (-155 / 351)), (0, 0), (152, (-70 / 351)), (0, 0), (0, 0), (0, 0), (0, 0), (150, (328 /
    1989)), (147, (-155 / 351)), (148, (-70 / 351)), (0, 0), (0, 0), (384, (155 / 351)), (385,
    (155 / 351)), (388, (155 / 351)), (389, (155 / 351)), (390, (155 / 351)), (427, (206 /
    5967)), (430, (206 / 5967)), (431, (206 / 5967)), (428, (-23 / 195)), (429, (-23 / 195)),
    (432, (-23 / 195)), (433, (-23 / 390)), (435, (206 / 5967)), (434, (-23 / 195)), (436, (206
    / 5967)), (0, 0), (490, (328 / 1989)), (0, 0), (503, (-7 / 2808)), (505, (-31 / 1404)), (0,
    0), (0, 0), (0, 0), (681, (31 / 1404)), (683, (31 / 1404)), (684, (31 / 1404)), (685, (7 /
    2808)), (688, (7 / 2808)), (689, (7 / 2808)), (686, (-749 / 14040)), (687, (-749 / 14040)),
    (690, (-749 / 14040)), (691, (-749 / 14040)), (692, (-101 / 477360)), (693, (-101 /
    477360)), (696, (-101 / 477360)), (697, (-101 / 477360)), (694, (-3 / 1040)), (695, (-3 /
    1040)), (698, (-3 / 1040)), (699, (-3 / 1040)), (806, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high6Records_checked : imageRecords
    L24HighPsi.destination60 GenusTwoPsiPullbacksReplay.squareThreeClaim = high6Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high6_checked : L24HighPsi.correctionCoordinates 6 = high6 := by
  change imageCoordinates L24HighPsi.destination60
    GenusTwoPsiPullbacksReplay.squareThreeClaim = _
  rw [imageCoordinates_eq_records, high6Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high7 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then 0 else (if i.val < 9 then (if i.val <
    7 then 0 else (if i.val < 8 then 1 else 0)) else 0)) else 0) else 0) else (if i.val < 75
    then (if i.val < 62 then 0 else (if i.val < 68 then (if i.val < 65 then 0 else (if i.val <
    66 then 0 else (if i.val < 67 then 0 else -1))) else (if i.val < 71 then (if i.val < 69 then
    0 else -1) else 0))) else 0)) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113
    then 0 else (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 0 else (if i.val
    < 115 then 1 else 0)) else 0) else 0)) else 0) else (if i.val < 177 then (if i.val < 164
    then (if i.val < 158 then (if i.val < 155 then 0 else (if i.val < 156 then (-155 / 351) else
    (if i.val < 157 then 0 else (-70 / 351)))) else (if i.val < 161 then (if i.val < 159 then
    (328 / 1989) else (if i.val < 160 then (-155 / 351) else 0)) else (if i.val < 162 then (-70
    / 351) else (if i.val < 163 then 0 else (328 / 1989))))) else (if i.val < 170 then (if i.val
    < 167 then (if i.val < 165 then (-155 / 351) else (if i.val < 166 then (-70 / 351) else 0))
    else (if i.val < 168 then (328 / 1989) else (if i.val < 169 then (-155 / 351) else (-70 /
    351)))) else 0)) else 0))) else (if i.val < 305 then 0 else (if i.val < 356 then 0 else (if
    i.val < 381 then 0 else (if i.val < 394 then (if i.val < 387 then 0 else (if i.val < 390
    then 0 else (if i.val < 392 then 0 else (if i.val < 393 then 0 else (155 / 351))))) else (if
    i.val < 400 then (if i.val < 397 then (155 / 351) else (if i.val < 398 then (155 / 351) else
    0)) else 0)))))) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if
    i.val < 432 then 0 else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then 0
    else (if i.val < 436 then 0 else (if i.val < 437 then 0 else (206 / 5967)))) else (if i.val
    < 441 then (if i.val < 439 then (206 / 5967) else (if i.val < 440 then (206 / 5967) else
    (-23 / 195))) else (if i.val < 443 then (-23 / 195) else (if i.val < 444 then (-23 / 390)
    else (206 / 5967))))) else (if i.val < 451 then (if i.val < 448 then (if i.val < 446 then
    (-23 / 195) else (if i.val < 447 then (206 / 5967) else 0)) else 0) else 0))) else (if i.val
    < 483 then 0 else (if i.val < 496 then (if i.val < 489 then 0 else (if i.val < 492 then (if
    i.val < 490 then 0 else (if i.val < 491 then 0 else (328 / 1989))) else 0)) else (if i.val <
    502 then 0 else (if i.val < 505 then 0 else (if i.val < 507 then (if i.val < 506 then 0 else
    (-7 / 2808)) else (if i.val < 508 then (-31 / 1404) else 0))))))) else 0) else (if i.val <
    713 then (if i.val < 662 then 0 else (if i.val < 687 then 0 else (if i.val < 700 then 0 else
    (if i.val < 706 then (if i.val < 703 then (if i.val < 701 then 0 else (31 / 1404)) else (if
    i.val < 704 then (31 / 1404) else (7 / 2808))) else (if i.val < 709 then (if i.val < 707
    then (7 / 2808) else (-749 / 14040)) else (if i.val < 711 then (-749 / 14040) else (-101 /
    477360))))))) else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val
    < 719 then (if i.val < 716 then (if i.val < 714 then (-101 / 477360) else (if i.val < 715
    then (-101 / 477360) else (-3 / 1040))) else (-3 / 1040)) else 0) else 0) else 0) else (if
    i.val < 789 then 0 else (if i.val < 802 then 0 else (if i.val < 808 then (if i.val < 805
    then 0 else (if i.val < 806 then 0 else (if i.val < 807 then 0 else (-1 / 56160)))) else
    0)))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high7Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (7, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (0, 0), (67, -1), (0, 0), (0, 0), (69, -1), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (70, -1), (0, 0), (0, 0), (114, 1), (0, 0), (155, (-155 / 351)),
    (0, 0), (0, 0), (157, (-70 / 351)), (0, 0), (0, 0), (0, 0), (158, (328 / 1989)), (159, (-155
    / 351)), (0, 0), (161, (-70 / 351)), (0, 0), (0, 0), (0, 0), (163, (328 / 1989)), (164,
    (-155 / 351)), (0, 0), (165, (-70 / 351)), (0, 0), (0, 0), (0, 0), (0, 0), (167, (328 /
    1989)), (168, (-155 / 351)), (169, (-70 / 351)), (0, 0), (0, 0), (393, (155 / 351)), (394,
    (155 / 351)), (395, (155 / 351)), (396, (155 / 351)), (397, (155 / 351)), (437, (206 /
    5967)), (438, (206 / 5967)), (439, (206 / 5967)), (440, (-23 / 195)), (441, (-23 / 195)),
    (442, (-23 / 195)), (443, (-23 / 390)), (444, (206 / 5967)), (445, (-23 / 195)), (446, (206
    / 5967)), (0, 0), (491, (328 / 1989)), (0, 0), (506, (-7 / 2808)), (507, (-31 / 1404)), (0,
    0), (0, 0), (0, 0), (701, (31 / 1404)), (702, (31 / 1404)), (703, (31 / 1404)), (704, (7 /
    2808)), (705, (7 / 2808)), (706, (7 / 2808)), (707, (-749 / 14040)), (708, (-749 / 14040)),
    (709, (-749 / 14040)), (710, (-749 / 14040)), (711, (-101 / 477360)), (712, (-101 /
    477360)), (713, (-101 / 477360)), (714, (-101 / 477360)), (715, (-3 / 1040)), (716, (-3 /
    1040)), (717, (-3 / 1040)), (718, (-3 / 1040)), (807, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high7Records_checked : imageRecords
    L24HighPsi.destination68 GenusTwoPsiPullbacksReplay.squareThreeClaim = high7Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high7_checked : L24HighPsi.correctionCoordinates 7 = high7 := by
  change imageCoordinates L24HighPsi.destination68
    GenusTwoPsiPullbacksReplay.squareThreeClaim = _
  rw [imageCoordinates_eq_records, high7Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high8 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then 0 else (if i.val < 9 then (if i.val <
    7 then 0 else (if i.val < 8 then 0 else 1)) else 0)) else 0) else 0) else (if i.val < 75
    then (if i.val < 62 then 0 else (if i.val < 68 then (if i.val < 65 then (if i.val < 63 then
    0 else (if i.val < 64 then 0 else -1)) else (if i.val < 66 then 0 else (if i.val < 67 then
    -1 else 0))) else (if i.val < 71 then (if i.val < 69 then 0 else -3) else 0))) else 0)) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then 0 else (if i.val < 119 then
    (if i.val < 116 then (if i.val < 114 then 0 else (if i.val < 115 then 3 else 0)) else 0)
    else 0)) else 0) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if
    i.val < 155 then 0 else (if i.val < 156 then (161 / 90) else (if i.val < 157 then (161 / 90)
    else (-40 / 9)))) else (if i.val < 161 then (if i.val < 159 then (206 / 51) else (161 / 90))
    else (if i.val < 162 then (-40 / 9) else (if i.val < 163 then (407 / 180) else (-7 / 36)))))
    else (if i.val < 170 then (if i.val < 167 then (if i.val < 165 then (407 / 180) else (if
    i.val < 166 then (-7 / 36) else (407 / 180))) else (if i.val < 168 then (-7 / 36) else (if
    i.val < 169 then (407 / 180) else (-7 / 36)))) else 0)) else 0))) else (if i.val < 305 then
    0 else (if i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val < 394 then (if
    i.val < 387 then 0 else (if i.val < 390 then 0 else (if i.val < 392 then (if i.val < 391
    then 0 else (-161 / 90)) else (if i.val < 393 then (-407 / 180) else (-161 / 90))))) else
    (if i.val < 400 then (if i.val < 397 then (if i.val < 395 then (-407 / 180) else (-25 / 9))
    else (if i.val < 398 then (-25 / 9) else 0)) else 0)))))) else (if i.val < 611 then (if
    i.val < 509 then (if i.val < 458 then (if i.val < 432 then 0 else (if i.val < 445 then (if
    i.val < 438 then (if i.val < 435 then 0 else (if i.val < 436 then 0 else (if i.val < 437
    then 0 else (62 / 153)))) else (if i.val < 441 then (-19 / 90) else (if i.val < 443 then (if
    i.val < 442 then (-19 / 90) else (-13 / 15)) else (if i.val < 444 then (-13 / 30) else (-19
    / 90))))) else (if i.val < 451 then (if i.val < 448 then (if i.val < 446 then (-19 / 90)
    else (if i.val < 447 then (7 / 18) else 0)) else 0) else 0))) else (if i.val < 483 then 0
    else (if i.val < 496 then (if i.val < 489 then 0 else (if i.val < 492 then (if i.val < 490
    then 0 else (if i.val < 491 then 0 else (206 / 51))) else 0)) else (if i.val < 502 then 0
    else (if i.val < 505 then 0 else (if i.val < 507 then (if i.val < 506 then 0 else (-7 / 36))
    else (67 / 720))))))) else 0) else (if i.val < 713 then (if i.val < 662 then 0 else (if
    i.val < 687 then 0 else (if i.val < 700 then 0 else (if i.val < 706 then (if i.val < 703
    then (if i.val < 701 then (-67 / 720) else (if i.val < 702 then (-67 / 720) else (-11 /
    72))) else (if i.val < 704 then (-11 / 72) else (if i.val < 705 then (7 / 36) else (-1 /
    40)))) else (if i.val < 709 then (-1 / 40) else (if i.val < 711 then (-37 / 90) else (473 /
    12240))))))) else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val <
    719 then (if i.val < 716 then (-1 / 180) else (if i.val < 717 then (-1 / 180) else (-37 /
    720))) else 0) else 0) else 0) else (if i.val < 789 then 0 else (if i.val < 802 then 0 else
    (if i.val < 808 then (if i.val < 805 then 0 else (if i.val < 806 then 0 else (if i.val < 807
    then 0 else (-1 / 720)))) else 0)))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high8Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (8, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (64, -1), (0, 0), (0, 0), (66, -1), (0, 0), (0, 0), (0, 0), (69, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (70, -3), (0, 0), (0, 0), (114, 3), (0, 0), (155, (161 /
    90)), (156, (161 / 90)), (0, 0), (157, (-40 / 9)), (0, 0), (0, 0), (0, 0), (158, (206 /
    51)), (159, (161 / 90)), (160, (161 / 90)), (161, (-40 / 9)), (0, 0), (0, 0), (162, (407 /
    180)), (163, (-7 / 36)), (164, (407 / 180)), (0, 0), (165, (-7 / 36)), (0, 0), (0, 0), (166,
    (407 / 180)), (0, 0), (167, (-7 / 36)), (168, (407 / 180)), (169, (-7 / 36)), (391, (-161 /
    90)), (392, (-407 / 180)), (393, (-161 / 90)), (394, (-407 / 180)), (395, (-25 / 9)), (396,
    (-25 / 9)), (397, (-25 / 9)), (437, (62 / 153)), (438, (-19 / 90)), (439, (-19 / 90)), (440,
    (-19 / 90)), (441, (-19 / 90)), (442, (-13 / 15)), (443, (-13 / 30)), (444, (-19 / 90)),
    (445, (-19 / 90)), (446, (7 / 18)), (0, 0), (491, (206 / 51)), (0, 0), (506, (-7 / 36)),
    (507, (67 / 720)), (508, (67 / 720)), (0, 0), (700, (-67 / 720)), (701, (-67 / 720)), (702,
    (-11 / 72)), (703, (-11 / 72)), (704, (7 / 36)), (705, (-1 / 40)), (706, (-1 / 40)), (707,
    (-1 / 40)), (708, (-1 / 40)), (709, (-37 / 90)), (710, (-37 / 90)), (711, (473 / 12240)),
    (712, (473 / 12240)), (713, (-1 / 180)), (714, (-1 / 180)), (715, (-1 / 180)), (716, (-1 /
    180)), (717, (-37 / 720)), (718, (-37 / 720)), (807, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high8Records_checked : imageRecords
    L24HighPsi.destination69 GenusTwoPsiPullbacksReplay.productThreeClaim = high8Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high8_checked : L24HighPsi.correctionCoordinates 8 = high8 := by
  change imageCoordinates L24HighPsi.destination69
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high8Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high9 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then 0 else (if i.val < 9 then 0 else (if
    i.val < 10 then 1 else 0))) else 0) else 0) else (if i.val < 75 then (if i.val < 62 then 0
    else (if i.val < 68 then (if i.val < 65 then 0 else (if i.val < 66 then -1 else 0)) else (if
    i.val < 71 then (if i.val < 69 then 0 else -1) else 0))) else 0)) else (if i.val < 152 then
    (if i.val < 126 then (if i.val < 113 then 0 else (if i.val < 119 then (if i.val < 116 then
    (if i.val < 114 then 0 else (if i.val < 115 then 1 else 0)) else 0) else 0)) else 0) else
    (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val < 155 then 0 else
    (if i.val < 156 then 0 else (if i.val < 157 then (-155 / 351) else (-70 / 351)))) else (if
    i.val < 161 then (if i.val < 159 then (328 / 1989) else (if i.val < 160 then 0 else (-155 /
    351))) else (if i.val < 162 then (-70 / 351) else (if i.val < 163 then (-155 / 351) else
    (-70 / 351))))) else (if i.val < 170 then (if i.val < 167 then (if i.val < 165 then 0 else
    (if i.val < 166 then (328 / 1989) else (-155 / 351))) else (if i.val < 168 then (-70 / 351)
    else (if i.val < 169 then 0 else (328 / 1989)))) else 0)) else 0))) else (if i.val < 305
    then 0 else (if i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val < 394 then (if
    i.val < 387 then 0 else (if i.val < 390 then 0 else (if i.val < 392 then (if i.val < 391
    then 0 else (155 / 351)) else (if i.val < 393 then (155 / 351) else 0)))) else (if i.val <
    400 then (if i.val < 397 then (if i.val < 395 then 0 else (155 / 351)) else (if i.val < 398
    then (155 / 351) else 0)) else 0)))))) else (if i.val < 611 then (if i.val < 509 then (if
    i.val < 458 then (if i.val < 432 then 0 else (if i.val < 445 then (if i.val < 438 then (if
    i.val < 435 then 0 else (if i.val < 436 then 0 else (if i.val < 437 then 0 else (206 /
    5967)))) else (if i.val < 441 then (if i.val < 439 then (-23 / 195) else (if i.val < 440
    then (-23 / 195) else (206 / 5967))) else (if i.val < 443 then (if i.val < 442 then (206 /
    5967) else (-23 / 195)) else (if i.val < 444 then (-23 / 390) else (-23 / 195))))) else (if
    i.val < 451 then (if i.val < 448 then (if i.val < 446 then (206 / 5967) else (if i.val < 447
    then (206 / 5967) else 0)) else 0) else 0))) else (if i.val < 483 then 0 else (if i.val <
    496 then (if i.val < 489 then 0 else (if i.val < 492 then (if i.val < 490 then 0 else (if
    i.val < 491 then 0 else (328 / 1989))) else 0)) else (if i.val < 502 then 0 else (if i.val <
    505 then 0 else (if i.val < 507 then (if i.val < 506 then 0 else (-7 / 2808)) else (if i.val
    < 508 then 0 else (-31 / 1404)))))))) else 0) else (if i.val < 713 then (if i.val < 662 then
    0 else (if i.val < 687 then 0 else (if i.val < 700 then 0 else (if i.val < 706 then (if
    i.val < 703 then (if i.val < 701 then (31 / 1404) else (if i.val < 702 then 0 else (31 /
    1404))) else (if i.val < 704 then (31 / 1404) else (if i.val < 705 then (7 / 2808) else
    (-749 / 14040)))) else (if i.val < 709 then (if i.val < 707 then (-749 / 14040) else (7 /
    2808)) else (if i.val < 711 then (-749 / 14040) else (-101 / 477360))))))) else (if i.val <
    764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then (if i.val < 716 then
    (if i.val < 714 then (-3 / 1040) else (if i.val < 715 then (-3 / 1040) else (-101 /
    477360))) else (if i.val < 717 then (-101 / 477360) else (-3 / 1040))) else 0) else 0) else
    0) else (if i.val < 789 then 0 else (if i.val < 802 then 0 else (if i.val < 808 then (if
    i.val < 805 then 0 else (if i.val < 806 then 0 else (if i.val < 807 then 0 else (-1 /
    56160)))) else 0)))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high9Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (9, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (0, 0), (65, -1), (0, 0), (0, 0), (69, -1), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (70, -1), (0, 0), (0, 0), (114, 1), (0, 0), (156, (-155 / 351)),
    (0, 0), (0, 0), (157, (-70 / 351)), (0, 0), (0, 0), (0, 0), (158, (328 / 1989)), (160, (-155
    / 351)), (0, 0), (161, (-70 / 351)), (0, 0), (0, 0), (0, 0), (169, (328 / 1989)), (166,
    (-155 / 351)), (0, 0), (167, (-70 / 351)), (0, 0), (0, 0), (0, 0), (0, 0), (165, (328 /
    1989)), (162, (-155 / 351)), (163, (-70 / 351)), (0, 0), (0, 0), (391, (155 / 351)), (392,
    (155 / 351)), (395, (155 / 351)), (396, (155 / 351)), (397, (155 / 351)), (437, (206 /
    5967)), (440, (206 / 5967)), (441, (206 / 5967)), (438, (-23 / 195)), (439, (-23 / 195)),
    (442, (-23 / 195)), (443, (-23 / 390)), (445, (206 / 5967)), (444, (-23 / 195)), (446, (206
    / 5967)), (0, 0), (491, (328 / 1989)), (0, 0), (506, (-7 / 2808)), (508, (-31 / 1404)), (0,
    0), (0, 0), (0, 0), (700, (31 / 1404)), (702, (31 / 1404)), (703, (31 / 1404)), (704, (7 /
    2808)), (707, (7 / 2808)), (708, (7 / 2808)), (705, (-749 / 14040)), (706, (-749 / 14040)),
    (709, (-749 / 14040)), (710, (-749 / 14040)), (711, (-101 / 477360)), (712, (-101 /
    477360)), (715, (-101 / 477360)), (716, (-101 / 477360)), (713, (-3 / 1040)), (714, (-3 /
    1040)), (717, (-3 / 1040)), (718, (-3 / 1040)), (807, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high9Records_checked : imageRecords
    L24HighPsi.destination71 GenusTwoPsiPullbacksReplay.squareThreeClaim = high9Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high9_checked : L24HighPsi.correctionCoordinates 9 = high9 := by
  change imageCoordinates L24HighPsi.destination71
    GenusTwoPsiPullbacksReplay.squareThreeClaim = _
  rw [imageCoordinates_eq_records, high9Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high10 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then (if i.val < 15 then (if i.val
    < 13 then 0 else (if i.val < 14 then 1 else 0)) else 0) else 0)) else 0) else (if i.val < 75
    then (if i.val < 62 then 0 else (if i.val < 68 then 0 else (if i.val < 71 then 0 else (if
    i.val < 73 then 0 else (if i.val < 74 then 0 else -1))))) else 0)) else (if i.val < 152 then
    0 else (if i.val < 177 then (if i.val < 164 then 0 else (if i.val < 170 then 0 else (if
    i.val < 173 then 0 else (if i.val < 175 then (if i.val < 174 then (-155 / 351) else 0) else
    (if i.val < 176 then (-70 / 351) else 0))))) else (if i.val < 190 then (if i.val < 183 then
    (if i.val < 180 then (if i.val < 178 then 0 else (if i.val < 179 then 0 else (328 / 1989)))
    else (if i.val < 181 then (-155 / 351) else (if i.val < 182 then (-70 / 351) else 0))) else
    0) else 0)))) else (if i.val < 305 then 0 else (if i.val < 356 then 0 else (if i.val < 381
    then 0 else (if i.val < 394 then 0 else (if i.val < 400 then (if i.val < 397 then 0 else (if
    i.val < 398 then 0 else (if i.val < 399 then (155 / 351) else 0))) else 0)))))) else (if
    i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then 0 else (if
    i.val < 445 then 0 else (if i.val < 451 then (if i.val < 448 then (if i.val < 446 then 0
    else (if i.val < 447 then 0 else (206 / 5967))) else (if i.val < 449 then (-23 / 195) else
    (if i.val < 450 then (-23 / 390) else 0))) else 0))) else (if i.val < 483 then 0 else (if
    i.val < 496 then (if i.val < 489 then 0 else (if i.val < 492 then 0 else (if i.val < 494
    then (if i.val < 493 then (328 / 1989) else 0) else 0))) else 0))) else (if i.val < 560 then
    (if i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if
    i.val < 510 then (-7 / 2808) else 0) else (if i.val < 513 then 0 else (if i.val < 514 then
    (-31 / 1404) else 0))) else 0) else 0) else 0) else 0)) else (if i.val < 713 then 0 else (if
    i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then 0 else (if
    i.val < 722 then (if i.val < 720 then (31 / 1404) else (if i.val < 721 then (7 / 2808) else
    (-749 / 14040))) else (if i.val < 723 then (-749 / 14040) else (-101 / 477360)))) else (if
    i.val < 731 then (if i.val < 728 then (if i.val < 726 then (-3 / 1040) else (if i.val < 727
    then (-3 / 1040) else 0)) else 0) else 0)) else 0) else (if i.val < 789 then 0 else (if
    i.val < 802 then 0 else (if i.val < 808 then 0 else (if i.val < 811 then (if i.val < 809
    then (-1 / 56160) else 0) else 0))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high10Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (13, 1), (0, 0), (0, 0), (0, 0), (74, -1), (0, 0), (173,
    (-155 / 351)), (0, 0), (175, (-70 / 351)), (0, 0), (0, 0), (0, 0), (179, (328 / 1989)),
    (180, (-155 / 351)), (181, (-70 / 351)), (398, (155 / 351)), (447, (206 / 5967)), (448, (-23
    / 195)), (449, (-23 / 390)), (0, 0), (492, (328 / 1989)), (0, 0), (509, (-7 / 2808)), (513,
    (-31 / 1404)), (0, 0), (719, (31 / 1404)), (720, (7 / 2808)), (721, (-749 / 14040)), (722,
    (-749 / 14040)), (723, (-101 / 477360)), (724, (-101 / 477360)), (725, (-3 / 1040)), (726,
    (-3 / 1040)), (808, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high10Records_checked : imageRecords
    L24HighPsi.destination93 GenusTwoPsiPullbacksReplay.squareTwoClaim = high10Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high10_checked : L24HighPsi.correctionCoordinates 10 = high10 := by
  change imageCoordinates L24HighPsi.destination93
    GenusTwoPsiPullbacksReplay.squareTwoClaim = _
  rw [imageCoordinates_eq_records, high10Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high11 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then (if i.val < 15 then (if i.val
    < 13 then 0 else (if i.val < 14 then 0 else 1)) else 0) else 0)) else 0) else (if i.val < 75
    then (if i.val < 62 then 0 else (if i.val < 68 then 0 else (if i.val < 71 then 0 else (if
    i.val < 73 then 0 else (if i.val < 74 then 0 else -3))))) else 0)) else (if i.val < 152 then
    0 else (if i.val < 177 then (if i.val < 164 then 0 else (if i.val < 170 then 0 else (if
    i.val < 173 then 0 else (if i.val < 175 then (161 / 90) else (if i.val < 176 then (-40 / 9)
    else 0))))) else (if i.val < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val <
    178 then 0 else (if i.val < 179 then (407 / 180) else (-7 / 36))) else (if i.val < 181 then
    (407 / 180) else (if i.val < 182 then (-7 / 36) else 0))) else 0) else 0)))) else (if i.val
    < 305 then 0 else (if i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val < 394
    then 0 else (if i.val < 400 then (if i.val < 397 then 0 else (if i.val < 398 then 0 else (if
    i.val < 399 then (-25 / 9) else 0))) else 0)))))) else (if i.val < 611 then (if i.val < 509
    then (if i.val < 458 then (if i.val < 432 then 0 else (if i.val < 445 then 0 else (if i.val
    < 451 then (if i.val < 448 then (if i.val < 446 then 0 else (if i.val < 447 then 0 else (-19
    / 90))) else (if i.val < 449 then (-19 / 90) else (if i.val < 450 then (-13 / 30) else 0)))
    else 0))) else (if i.val < 483 then 0 else (if i.val < 496 then (if i.val < 489 then 0 else
    (if i.val < 492 then 0 else (if i.val < 494 then (if i.val < 493 then (206 / 51) else 0)
    else 0))) else 0))) else (if i.val < 560 then (if i.val < 534 then (if i.val < 521 then (if
    i.val < 515 then (if i.val < 512 then (if i.val < 510 then (-7 / 36) else 0) else (if i.val
    < 513 then 0 else (67 / 720))) else 0) else 0) else 0) else 0)) else (if i.val < 713 then 0
    else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then 0
    else (if i.val < 722 then (if i.val < 720 then (-11 / 72) else (-1 / 40)) else (if i.val <
    723 then (-37 / 90) else (if i.val < 724 then (473 / 12240) else (-1 / 180))))) else (if
    i.val < 731 then (if i.val < 728 then (if i.val < 726 then (-1 / 180) else (if i.val < 727
    then (-37 / 720) else 0)) else 0) else 0)) else 0) else (if i.val < 789 then 0 else (if
    i.val < 802 then 0 else (if i.val < 808 then 0 else (if i.val < 811 then (if i.val < 809
    then (-1 / 720) else 0) else 0))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high11Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (14, 1), (0, 0), (0, 0), (74, -3), (0, 0), (173, (161
    / 90)), (174, (161 / 90)), (175, (-40 / 9)), (0, 0), (0, 0), (178, (407 / 180)), (179, (-7 /
    36)), (180, (407 / 180)), (181, (-7 / 36)), (398, (-25 / 9)), (447, (-19 / 90)), (448, (-19
    / 90)), (449, (-13 / 30)), (0, 0), (492, (206 / 51)), (0, 0), (509, (-7 / 36)), (513, (67 /
    720)), (514, (67 / 720)), (719, (-11 / 72)), (720, (-1 / 40)), (721, (-1 / 40)), (722, (-37
    / 90)), (723, (473 / 12240)), (724, (-1 / 180)), (725, (-1 / 180)), (726, (-37 / 720)),
    (808, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high11Records_checked : imageRecords
    L24HighPsi.destination94 GenusTwoPsiProduct.requested = high11Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high11_checked : L24HighPsi.correctionCoordinates 11 = high11 := by
  change imageCoordinates L24HighPsi.destination94
    GenusTwoPsiProduct.requested = _
  rw [imageCoordinates_eq_records, high11Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high12 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then (if i.val < 15 then 0 else
    (if i.val < 16 then 1 else 0)) else 0)) else 0) else (if i.val < 75 then (if i.val < 62 then
    0 else (if i.val < 68 then 0 else (if i.val < 71 then (if i.val < 69 then -1 else 0) else
    0))) else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then 0 else (if i.val < 79
    then -1 else 0)) else (if i.val < 84 then (if i.val < 82 then -1 else 0) else 0)) else 0)))
    else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then 0 else (if i.val < 119
    then (if i.val < 116 then (if i.val < 114 then 0 else (if i.val < 115 then 1 else 0)) else
    0) else 0)) else 0) else (if i.val < 177 then 0 else (if i.val < 190 then (if i.val < 183
    then (if i.val < 180 then 0 else (if i.val < 181 then 0 else (if i.val < 182 then 0 else
    (-155 / 351)))) else (if i.val < 186 then (if i.val < 184 then 0 else (if i.val < 185 then 0
    else (-70 / 351))) else (if i.val < 188 then (if i.val < 187 then 0 else (328 / 1989)) else
    (if i.val < 189 then (-155 / 351) else 0)))) else (if i.val < 196 then (if i.val < 193 then
    (if i.val < 191 then (-70 / 351) else (if i.val < 192 then 0 else (328 / 1989))) else (if
    i.val < 194 then (-155 / 351) else (if i.val < 195 then 0 else (-70 / 351)))) else (if i.val
    < 199 then (if i.val < 197 then 0 else (if i.val < 198 then 0 else (328 / 1989))) else (if
    i.val < 201 then (if i.val < 200 then (-155 / 351) else (-70 / 351)) else 0))))))) else (if
    i.val < 305 then 0 else (if i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val <
    394 then 0 else (if i.val < 400 then (if i.val < 397 then (if i.val < 395 then 0 else (155 /
    351)) else 0) else (if i.val < 403 then (if i.val < 401 then 0 else (155 / 351)) else (if
    i.val < 405 then (if i.val < 404 then (155 / 351) else 0) else 0)))))))) else (if i.val <
    611 then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then 0 else (if i.val <
    445 then 0 else (if i.val < 451 then (if i.val < 448 then 0 else (if i.val < 449 then 0 else
    (if i.val < 450 then 0 else (206 / 5967)))) else (if i.val < 454 then (if i.val < 452 then
    (206 / 5967) else (if i.val < 453 then (206 / 5967) else (-23 / 195))) else (if i.val < 456
    then (-23 / 195) else (if i.val < 457 then (-23 / 390) else (206 / 5967))))))) else (if
    i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val < 461 then (if i.val <
    459 then (-23 / 195) else (if i.val < 460 then (206 / 5967) else 0)) else 0) else 0) else 0)
    else (if i.val < 496 then (if i.val < 489 then 0 else (if i.val < 492 then 0 else (if i.val
    < 494 then (if i.val < 493 then 0 else (328 / 1989)) else 0))) else 0))) else (if i.val <
    560 then (if i.val < 534 then (if i.val < 521 then (if i.val < 515 then 0 else (if i.val <
    518 then (if i.val < 516 then (-7 / 2808) else (if i.val < 517 then (-31 / 1404) else 0))
    else 0)) else 0) else 0) else 0)) else (if i.val < 713 then (if i.val < 662 then 0 else (if
    i.val < 687 then 0 else (if i.val < 700 then 0 else (if i.val < 706 then (if i.val < 703
    then (if i.val < 701 then 0 else (if i.val < 702 then 0 else (31 / 1404))) else 0) else
    0)))) else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then 0 else (if i.val <
    731 then (if i.val < 728 then 0 else (if i.val < 729 then (31 / 1404) else (if i.val < 730
    then (31 / 1404) else (7 / 2808)))) else (if i.val < 734 then (if i.val < 732 then (7 /
    2808) else (if i.val < 733 then (7 / 2808) else (-749 / 14040))) else (if i.val < 736 then
    (-749 / 14040) else (if i.val < 737 then (-749 / 14040) else (-101 / 477360)))))) else (if
    i.val < 751 then (if i.val < 744 then (if i.val < 741 then (-101 / 477360) else (-3 / 1040))
    else (if i.val < 747 then (if i.val < 745 then (-3 / 1040) else 0) else 0)) else 0)) else
    (if i.val < 789 then 0 else (if i.val < 802 then 0 else (if i.val < 808 then 0 else (if
    i.val < 811 then (if i.val < 809 then 0 else (if i.val < 810 then (-1 / 56160) else 0)) else
    0))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high12Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (15, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (0, 0), (78, -1), (0, 0), (0, 0), (68, -1), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (81, -1), (0, 0), (0, 0), (114, 1), (0, 0), (182, (-155 / 351)),
    (0, 0), (0, 0), (185, (-70 / 351)), (0, 0), (0, 0), (0, 0), (187, (328 / 1989)), (188, (-155
    / 351)), (0, 0), (190, (-70 / 351)), (0, 0), (0, 0), (0, 0), (192, (328 / 1989)), (193,
    (-155 / 351)), (0, 0), (195, (-70 / 351)), (0, 0), (0, 0), (0, 0), (0, 0), (198, (328 /
    1989)), (199, (-155 / 351)), (200, (-70 / 351)), (0, 0), (0, 0), (401, (155 / 351)), (402,
    (155 / 351)), (395, (155 / 351)), (396, (155 / 351)), (403, (155 / 351)), (450, (206 /
    5967)), (451, (206 / 5967)), (452, (206 / 5967)), (453, (-23 / 195)), (454, (-23 / 195)),
    (455, (-23 / 195)), (456, (-23 / 390)), (457, (206 / 5967)), (458, (-23 / 195)), (459, (206
    / 5967)), (0, 0), (493, (328 / 1989)), (0, 0), (515, (-7 / 2808)), (516, (-31 / 1404)), (0,
    0), (0, 0), (0, 0), (728, (31 / 1404)), (702, (31 / 1404)), (729, (31 / 1404)), (730, (7 /
    2808)), (731, (7 / 2808)), (732, (7 / 2808)), (733, (-749 / 14040)), (734, (-749 / 14040)),
    (735, (-749 / 14040)), (736, (-749 / 14040)), (737, (-101 / 477360)), (738, (-101 /
    477360)), (739, (-101 / 477360)), (740, (-101 / 477360)), (741, (-3 / 1040)), (742, (-3 /
    1040)), (743, (-3 / 1040)), (744, (-3 / 1040)), (809, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high12Records_checked : imageRecords
    L24HighPsi.destination101 GenusTwoPsiPullbacksReplay.squareThreeClaim = high12Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high12_checked : L24HighPsi.correctionCoordinates 12 = high12 := by
  change imageCoordinates L24HighPsi.destination101
    GenusTwoPsiPullbacksReplay.squareThreeClaim = _
  rw [imageCoordinates_eq_records, high12Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high13 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then (if i.val < 15 then 0 else
    (if i.val < 16 then 0 else (if i.val < 17 then 1 else 0))) else 0)) else 0) else (if i.val <
    75 then (if i.val < 62 then 0 else (if i.val < 68 then 0 else (if i.val < 71 then (if i.val
    < 69 then -3 else 0) else 0))) else (if i.val < 88 then (if i.val < 81 then (if i.val < 78
    then (if i.val < 76 then -1 else (if i.val < 77 then 0 else -1)) else 0) else (if i.val < 84
    then (if i.val < 82 then -3 else 0) else 0)) else 0))) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then 0 else (if i.val < 119 then (if i.val < 116 then (if i.val <
    114 then 0 else (if i.val < 115 then 3 else 0)) else 0) else 0)) else 0) else (if i.val <
    177 then 0 else (if i.val < 190 then (if i.val < 183 then (if i.val < 180 then 0 else (if
    i.val < 181 then 0 else (if i.val < 182 then 0 else (161 / 90)))) else (if i.val < 186 then
    (if i.val < 184 then (161 / 90) else (if i.val < 185 then 0 else (-40 / 9))) else (if i.val
    < 188 then (if i.val < 187 then 0 else (206 / 51)) else (161 / 90)))) else (if i.val < 196
    then (if i.val < 193 then (if i.val < 191 then (-40 / 9) else (if i.val < 192 then (407 /
    180) else (-7 / 36))) else (if i.val < 194 then (407 / 180) else (if i.val < 195 then 0 else
    (-7 / 36)))) else (if i.val < 199 then (if i.val < 197 then (407 / 180) else (if i.val < 198
    then 0 else (-7 / 36))) else (if i.val < 201 then (if i.val < 200 then (407 / 180) else (-7
    / 36)) else 0))))))) else (if i.val < 305 then 0 else (if i.val < 356 then 0 else (if i.val
    < 381 then 0 else (if i.val < 394 then 0 else (if i.val < 400 then (if i.val < 397 then (if
    i.val < 395 then 0 else (-25 / 9)) else (if i.val < 398 then 0 else (if i.val < 399 then 0
    else (-161 / 90)))) else (if i.val < 403 then (if i.val < 401 then (-407 / 180) else (if
    i.val < 402 then (-161 / 90) else (-407 / 180))) else (if i.val < 405 then (if i.val < 404
    then (-25 / 9) else 0) else 0)))))))) else (if i.val < 611 then (if i.val < 509 then (if
    i.val < 458 then (if i.val < 432 then 0 else (if i.val < 445 then 0 else (if i.val < 451
    then (if i.val < 448 then 0 else (if i.val < 449 then 0 else (if i.val < 450 then 0 else (62
    / 153)))) else (if i.val < 454 then (-19 / 90) else (if i.val < 456 then (if i.val < 455
    then (-19 / 90) else (-13 / 15)) else (if i.val < 457 then (-13 / 30) else (-19 / 90)))))))
    else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val < 461 then (if
    i.val < 459 then (-19 / 90) else (if i.val < 460 then (7 / 18) else 0)) else 0) else 0) else
    0) else (if i.val < 496 then (if i.val < 489 then 0 else (if i.val < 492 then 0 else (if
    i.val < 494 then (if i.val < 493 then 0 else (206 / 51)) else 0))) else 0))) else (if i.val
    < 560 then (if i.val < 534 then (if i.val < 521 then (if i.val < 515 then 0 else (if i.val <
    518 then (if i.val < 516 then (-7 / 36) else (67 / 720)) else 0)) else 0) else 0) else 0))
    else (if i.val < 713 then (if i.val < 662 then 0 else (if i.val < 687 then 0 else (if i.val
    < 700 then 0 else (if i.val < 706 then (if i.val < 703 then (if i.val < 701 then 0 else (if
    i.val < 702 then 0 else (-11 / 72))) else 0) else 0)))) else (if i.val < 764 then (if i.val
    < 738 then (if i.val < 725 then 0 else (if i.val < 731 then (if i.val < 728 then (if i.val <
    726 then 0 else (if i.val < 727 then 0 else (-67 / 720))) else (if i.val < 729 then (-67 /
    720) else (if i.val < 730 then (-11 / 72) else (7 / 36)))) else (if i.val < 734 then (-1 /
    40) else (if i.val < 736 then (if i.val < 735 then (-1 / 40) else (-37 / 90)) else (if i.val
    < 737 then (-37 / 90) else (473 / 12240)))))) else (if i.val < 751 then (if i.val < 744 then
    (if i.val < 741 then (if i.val < 739 then (473 / 12240) else (-1 / 180)) else (if i.val <
    742 then (-1 / 180) else (if i.val < 743 then (-1 / 180) else (-37 / 720)))) else (if i.val
    < 747 then (if i.val < 745 then (-37 / 720) else 0) else 0)) else 0)) else (if i.val < 789
    then 0 else (if i.val < 802 then 0 else (if i.val < 808 then 0 else (if i.val < 811 then (if
    i.val < 809 then 0 else (if i.val < 810 then (-1 / 720) else 0)) else 0))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high13Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (16, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (75, -1), (0, 0), (0, 0), (77, -1), (0, 0), (0, 0), (0, 0), (68, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (81, -3), (0, 0), (0, 0), (114, 3), (0, 0), (182, (161 /
    90)), (183, (161 / 90)), (0, 0), (185, (-40 / 9)), (0, 0), (0, 0), (0, 0), (187, (206 /
    51)), (188, (161 / 90)), (189, (161 / 90)), (190, (-40 / 9)), (0, 0), (0, 0), (191, (407 /
    180)), (192, (-7 / 36)), (193, (407 / 180)), (0, 0), (195, (-7 / 36)), (0, 0), (0, 0), (196,
    (407 / 180)), (0, 0), (198, (-7 / 36)), (199, (407 / 180)), (200, (-7 / 36)), (399, (-161 /
    90)), (400, (-407 / 180)), (401, (-161 / 90)), (402, (-407 / 180)), (395, (-25 / 9)), (396,
    (-25 / 9)), (403, (-25 / 9)), (450, (62 / 153)), (451, (-19 / 90)), (452, (-19 / 90)), (453,
    (-19 / 90)), (454, (-19 / 90)), (455, (-13 / 15)), (456, (-13 / 30)), (457, (-19 / 90)),
    (458, (-19 / 90)), (459, (7 / 18)), (0, 0), (493, (206 / 51)), (0, 0), (515, (-7 / 36)),
    (516, (67 / 720)), (517, (67 / 720)), (0, 0), (727, (-67 / 720)), (728, (-67 / 720)), (702,
    (-11 / 72)), (729, (-11 / 72)), (730, (7 / 36)), (731, (-1 / 40)), (732, (-1 / 40)), (733,
    (-1 / 40)), (734, (-1 / 40)), (735, (-37 / 90)), (736, (-37 / 90)), (737, (473 / 12240)),
    (738, (473 / 12240)), (739, (-1 / 180)), (740, (-1 / 180)), (741, (-1 / 180)), (742, (-1 /
    180)), (743, (-37 / 720)), (744, (-37 / 720)), (809, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high13Records_checked : imageRecords
    L24HighPsi.destination102 GenusTwoPsiPullbacksReplay.productThreeClaim = high13Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high13_checked : L24HighPsi.correctionCoordinates 13 = high13 := by
  change imageCoordinates L24HighPsi.destination102
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high13Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high14 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then (if i.val < 15 then 0 else
    (if i.val < 16 then 0 else (if i.val < 17 then 0 else 1))) else 0)) else 0) else (if i.val <
    75 then (if i.val < 62 then 0 else (if i.val < 68 then 0 else (if i.val < 71 then (if i.val
    < 69 then 0 else (if i.val < 70 then -1 else 0)) else 0))) else (if i.val < 88 then (if
    i.val < 81 then (if i.val < 78 then (if i.val < 76 then -1 else 0) else (if i.val < 79 then
    -3 else 0)) else (if i.val < 84 then (if i.val < 82 then -3 else 0) else 0)) else 0))) else
    (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then 0 else (if i.val < 119 then
    (if i.val < 116 then 0 else (if i.val < 117 then 3 else 0)) else 0)) else 0) else (if i.val
    < 177 then 0 else (if i.val < 190 then (if i.val < 183 then (if i.val < 180 then 0 else (if
    i.val < 181 then 0 else (if i.val < 182 then 0 else (161 / 90)))) else (if i.val < 186 then
    (if i.val < 184 then 0 else (if i.val < 185 then (161 / 90) else (-40 / 9))) else (if i.val
    < 188 then (if i.val < 187 then (407 / 180) else (-7 / 36)) else (if i.val < 189 then (407 /
    180) else 0)))) else (if i.val < 196 then (if i.val < 193 then (if i.val < 191 then (-7 /
    36) else (if i.val < 192 then 0 else (206 / 51))) else (if i.val < 194 then (161 / 90) else
    (if i.val < 195 then (161 / 90) else (-40 / 9)))) else (if i.val < 199 then (if i.val < 197
    then 0 else (if i.val < 198 then (407 / 180) else (-7 / 36))) else (if i.val < 201 then (if
    i.val < 200 then (407 / 180) else (-7 / 36)) else 0))))))) else (if i.val < 305 then 0 else
    (if i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val < 394 then 0 else (if
    i.val < 400 then (if i.val < 397 then (if i.val < 395 then 0 else (if i.val < 396 then (-161
    / 90) else (-407 / 180))) else (if i.val < 398 then 0 else (if i.val < 399 then 0 else (-161
    / 90)))) else (if i.val < 403 then (if i.val < 401 then (-407 / 180) else (-25 / 9)) else
    (if i.val < 405 then (if i.val < 404 then (-25 / 9) else 0) else 0)))))))) else (if i.val <
    611 then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then 0 else (if i.val <
    445 then 0 else (if i.val < 451 then (if i.val < 448 then 0 else (if i.val < 449 then 0 else
    (if i.val < 450 then 0 else (-19 / 90)))) else (if i.val < 454 then (if i.val < 452 then (62
    / 153) else (-19 / 90)) else (if i.val < 456 then (if i.val < 455 then (-13 / 15) else (-19
    / 90)) else (if i.val < 457 then (-13 / 30) else (7 / 18))))))) else (if i.val < 483 then
    (if i.val < 470 then (if i.val < 464 then (if i.val < 461 then (if i.val < 459 then (-19 /
    90) else (if i.val < 460 then (-19 / 90) else 0)) else 0) else 0) else 0) else (if i.val <
    496 then (if i.val < 489 then 0 else (if i.val < 492 then 0 else (if i.val < 494 then (if
    i.val < 493 then 0 else (206 / 51)) else 0))) else 0))) else (if i.val < 560 then (if i.val
    < 534 then (if i.val < 521 then (if i.val < 515 then 0 else (if i.val < 518 then (if i.val <
    516 then (-7 / 36) else (if i.val < 517 then (67 / 720) else 0)) else (if i.val < 519 then
    (67 / 720) else 0))) else 0) else 0) else 0)) else (if i.val < 713 then (if i.val < 662 then
    0 else (if i.val < 687 then 0 else (if i.val < 700 then 0 else (if i.val < 706 then (if
    i.val < 703 then (if i.val < 701 then 0 else (if i.val < 702 then 0 else (-67 / 720))) else
    0) else 0)))) else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then 0 else (if
    i.val < 731 then (if i.val < 728 then (if i.val < 726 then 0 else (if i.val < 727 then 0
    else (-67 / 720))) else (if i.val < 729 then (-11 / 72) else (if i.val < 730 then (-11 / 72)
    else (-1 / 40)))) else (if i.val < 734 then (if i.val < 732 then (7 / 36) else (-1 / 40))
    else (if i.val < 736 then (if i.val < 735 then (-37 / 90) else (-1 / 40)) else (if i.val <
    737 then (-37 / 90) else (473 / 12240)))))) else (if i.val < 751 then (if i.val < 744 then
    (if i.val < 741 then (if i.val < 739 then (-1 / 180) else (if i.val < 740 then (473 / 12240)
    else (-1 / 180))) else (if i.val < 742 then (-1 / 180) else (if i.val < 743 then (-37 / 720)
    else (-1 / 180)))) else (if i.val < 747 then (if i.val < 745 then (-37 / 720) else 0) else
    0)) else 0)) else (if i.val < 789 then 0 else (if i.val < 802 then 0 else (if i.val < 808
    then 0 else (if i.val < 811 then (if i.val < 809 then 0 else (if i.val < 810 then (-1 / 720)
    else 0)) else 0))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high14Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (17, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (75, -1), (0, 0), (0, 0), (69, -1), (0, 0), (0, 0), (0, 0), (78, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (81, -3), (0, 0), (0, 0), (116, 3), (0, 0), (182, (161 /
    90)), (184, (161 / 90)), (0, 0), (185, (-40 / 9)), (0, 0), (0, 0), (0, 0), (192, (206 /
    51)), (193, (161 / 90)), (194, (161 / 90)), (195, (-40 / 9)), (0, 0), (0, 0), (186, (407 /
    180)), (187, (-7 / 36)), (188, (407 / 180)), (0, 0), (190, (-7 / 36)), (0, 0), (0, 0), (197,
    (407 / 180)), (0, 0), (198, (-7 / 36)), (199, (407 / 180)), (200, (-7 / 36)), (399, (-161 /
    90)), (400, (-407 / 180)), (395, (-161 / 90)), (396, (-407 / 180)), (401, (-25 / 9)), (402,
    (-25 / 9)), (403, (-25 / 9)), (451, (62 / 153)), (450, (-19 / 90)), (452, (-19 / 90)), (453,
    (-19 / 90)), (455, (-19 / 90)), (454, (-13 / 15)), (456, (-13 / 30)), (459, (-19 / 90)),
    (458, (-19 / 90)), (457, (7 / 18)), (0, 0), (493, (206 / 51)), (0, 0), (515, (-7 / 36)),
    (516, (67 / 720)), (518, (67 / 720)), (0, 0), (727, (-67 / 720)), (702, (-67 / 720)), (728,
    (-11 / 72)), (729, (-11 / 72)), (731, (7 / 36)), (730, (-1 / 40)), (732, (-1 / 40)), (733,
    (-1 / 40)), (735, (-1 / 40)), (734, (-37 / 90)), (736, (-37 / 90)), (737, (473 / 12240)),
    (739, (473 / 12240)), (738, (-1 / 180)), (740, (-1 / 180)), (741, (-1 / 180)), (743, (-1 /
    180)), (742, (-37 / 720)), (744, (-37 / 720)), (809, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high14Records_checked : imageRecords
    L24HighPsi.destination103 GenusTwoPsiPullbacksReplay.productThreeClaim = high14Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high14_checked : L24HighPsi.correctionCoordinates 14 = high14 := by
  change imageCoordinates L24HighPsi.destination103
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high14Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high15 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then 0 else (if i.val < 21 then
    (if i.val < 19 then 1 else 0) else 0))) else 0) else (if i.val < 75 then (if i.val < 62 then
    0 else (if i.val < 68 then 0 else (if i.val < 71 then (if i.val < 69 then 0 else (if i.val <
    70 then -1 else 0)) else 0))) else (if i.val < 88 then (if i.val < 81 then (if i.val < 78
    then (if i.val < 76 then 0 else (if i.val < 77 then -3 else -1)) else 0) else (if i.val < 84
    then (if i.val < 82 then -3 else 0) else 0)) else 0))) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then 0 else (if i.val < 119 then (if i.val < 116 then (if i.val <
    114 then 0 else (if i.val < 115 then 0 else 3)) else 0) else 0)) else 0) else (if i.val <
    177 then 0 else (if i.val < 190 then (if i.val < 183 then 0 else (if i.val < 186 then (if
    i.val < 184 then (161 / 90) else (if i.val < 185 then (161 / 90) else (-40 / 9))) else (if
    i.val < 188 then (if i.val < 187 then (407 / 180) else (-7 / 36)) else (if i.val < 189 then
    0 else (407 / 180))))) else (if i.val < 196 then (if i.val < 193 then (if i.val < 191 then
    (-7 / 36) else (if i.val < 192 then (407 / 180) else (-7 / 36))) else (if i.val < 194 then 0
    else (if i.val < 195 then (407 / 180) else (-7 / 36)))) else (if i.val < 199 then (if i.val
    < 197 then (161 / 90) else (if i.val < 198 then (161 / 90) else (-40 / 9))) else (if i.val <
    201 then (if i.val < 200 then 0 else (206 / 51)) else 0))))))) else (if i.val < 305 then 0
    else (if i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val < 394 then 0 else (if
    i.val < 400 then (if i.val < 397 then (if i.val < 395 then 0 else (if i.val < 396 then (-161
    / 90) else (-407 / 180))) else (if i.val < 398 then 0 else (if i.val < 399 then 0 else (-25
    / 9)))) else (if i.val < 403 then (if i.val < 401 then (-25 / 9) else (if i.val < 402 then
    (-161 / 90) else (-407 / 180))) else (if i.val < 405 then (if i.val < 404 then (-25 / 9)
    else 0) else 0)))))))) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then
    (if i.val < 432 then 0 else (if i.val < 445 then 0 else (if i.val < 451 then (if i.val < 448
    then 0 else (if i.val < 449 then 0 else (if i.val < 450 then 0 else (-19 / 90)))) else (if
    i.val < 454 then (if i.val < 452 then (-19 / 90) else (if i.val < 453 then (-13 / 15) else
    (62 / 153))) else (if i.val < 456 then (-19 / 90) else (if i.val < 457 then (-13 / 30) else
    (-19 / 90))))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if
    i.val < 461 then (if i.val < 459 then (7 / 18) else (if i.val < 460 then (-19 / 90) else 0))
    else 0) else 0) else 0) else (if i.val < 496 then (if i.val < 489 then 0 else (if i.val <
    492 then 0 else (if i.val < 494 then (if i.val < 493 then 0 else (206 / 51)) else 0))) else
    0))) else (if i.val < 560 then (if i.val < 534 then (if i.val < 521 then (if i.val < 515
    then 0 else (if i.val < 518 then (if i.val < 516 then (-7 / 36) else (if i.val < 517 then 0
    else (67 / 720))) else (if i.val < 519 then (67 / 720) else 0))) else 0) else 0) else 0))
    else (if i.val < 713 then (if i.val < 662 then 0 else (if i.val < 687 then 0 else (if i.val
    < 700 then 0 else (if i.val < 706 then (if i.val < 703 then (if i.val < 701 then 0 else (if
    i.val < 702 then 0 else (-67 / 720))) else 0) else 0)))) else (if i.val < 764 then (if i.val
    < 738 then (if i.val < 725 then 0 else (if i.val < 731 then (if i.val < 728 then (if i.val <
    726 then 0 else (if i.val < 727 then 0 else (-11 / 72))) else (if i.val < 729 then (-67 /
    720) else (if i.val < 730 then (-11 / 72) else (-1 / 40)))) else (if i.val < 734 then (if
    i.val < 732 then (-1 / 40) else (if i.val < 733 then (-37 / 90) else (7 / 36))) else (if
    i.val < 736 then (-1 / 40) else (if i.val < 737 then (-37 / 90) else (473 / 12240)))))) else
    (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then (-1 /
    180) else (if i.val < 740 then (-1 / 180) else (-37 / 720))) else (if i.val < 742 then (473
    / 12240) else (-1 / 180))) else (if i.val < 747 then (if i.val < 745 then (-37 / 720) else
    0) else 0)) else 0)) else (if i.val < 789 then 0 else (if i.val < 802 then 0 else (if i.val
    < 808 then 0 else (if i.val < 811 then (if i.val < 809 then 0 else (if i.val < 810 then (-1
    / 720) else 0)) else 0))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high15Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (18, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (77, -1), (0, 0), (0, 0), (69, -1), (0, 0), (0, 0), (0, 0), (76, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (81, -3), (0, 0), (0, 0), (115, 3), (0, 0), (183, (161 /
    90)), (184, (161 / 90)), (0, 0), (185, (-40 / 9)), (0, 0), (0, 0), (0, 0), (200, (206 /
    51)), (196, (161 / 90)), (197, (161 / 90)), (198, (-40 / 9)), (0, 0), (0, 0), (186, (407 /
    180)), (187, (-7 / 36)), (189, (407 / 180)), (0, 0), (190, (-7 / 36)), (0, 0), (0, 0), (194,
    (407 / 180)), (0, 0), (195, (-7 / 36)), (191, (407 / 180)), (192, (-7 / 36)), (401, (-161 /
    90)), (402, (-407 / 180)), (395, (-161 / 90)), (396, (-407 / 180)), (399, (-25 / 9)), (400,
    (-25 / 9)), (403, (-25 / 9)), (453, (62 / 153)), (450, (-19 / 90)), (454, (-19 / 90)), (451,
    (-19 / 90)), (455, (-19 / 90)), (452, (-13 / 15)), (456, (-13 / 30)), (459, (-19 / 90)),
    (457, (-19 / 90)), (458, (7 / 18)), (0, 0), (493, (206 / 51)), (0, 0), (515, (-7 / 36)),
    (517, (67 / 720)), (518, (67 / 720)), (0, 0), (728, (-67 / 720)), (702, (-67 / 720)), (727,
    (-11 / 72)), (729, (-11 / 72)), (733, (7 / 36)), (730, (-1 / 40)), (734, (-1 / 40)), (731,
    (-1 / 40)), (735, (-1 / 40)), (732, (-37 / 90)), (736, (-37 / 90)), (737, (473 / 12240)),
    (741, (473 / 12240)), (738, (-1 / 180)), (742, (-1 / 180)), (739, (-1 / 180)), (743, (-1 /
    180)), (740, (-37 / 720)), (744, (-37 / 720)), (809, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high15Records_checked : imageRecords
    L24HighPsi.destination105 GenusTwoPsiPullbacksReplay.productThreeClaim = high15Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high15_checked : L24HighPsi.correctionCoordinates 15 = high15 := by
  change imageCoordinates L24HighPsi.destination105
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high15Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high16 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then 0 else (if i.val < 21 then
    (if i.val < 19 then 0 else (if i.val < 20 then 1 else 0)) else 0))) else 0) else (if i.val <
    75 then (if i.val < 62 then (if i.val < 56 then 0 else (if i.val < 59 then 0 else (if i.val
    < 60 then 0 else (if i.val < 61 then 0 else -1)))) else 0) else (if i.val < 88 then (if
    i.val < 81 then 0 else (if i.val < 84 then 0 else (if i.val < 86 then (if i.val < 85 then 0
    else -1) else 0))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then -1 else
    0) else 0) else 0)))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then
    (if i.val < 107 then 0 else (if i.val < 110 then 0 else (if i.val < 111 then 0 else (if
    i.val < 112 then 1 else 0)))) else 0) else 0) else (if i.val < 177 then 0 else (if i.val <
    190 then 0 else (if i.val < 196 then 0 else (if i.val < 199 then 0 else (if i.val < 201 then
    0 else (if i.val < 202 then (-155 / 351) else 0)))))))) else (if i.val < 305 then (if i.val
    < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val < 206
    then (if i.val < 204 then 0 else (if i.val < 205 then (-70 / 351) else 0)) else (if i.val <
    207 then (328 / 1989) else (if i.val < 208 then (-155 / 351) else 0))) else (if i.val < 212
    then (if i.val < 210 then (-70 / 351) else (if i.val < 211 then 0 else (328 / 1989))) else
    (if i.val < 213 then (-155 / 351) else (if i.val < 214 then 0 else (-70 / 351))))) else (if
    i.val < 221 then (if i.val < 218 then (if i.val < 216 then 0 else (if i.val < 217 then 0
    else (328 / 1989))) else (if i.val < 219 then (-155 / 351) else (if i.val < 220 then (-70 /
    351) else 0))) else 0)) else 0) else 0) else (if i.val < 356 then 0 else (if i.val < 381
    then 0 else (if i.val < 394 then (if i.val < 387 then 0 else (if i.val < 390 then (if i.val
    < 388 then 0 else (155 / 351)) else 0)) else (if i.val < 400 then 0 else (if i.val < 403
    then 0 else (if i.val < 405 then 0 else (if i.val < 406 then 0 else (155 / 351))))))))))
    else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if
    i.val < 419 then (if i.val < 413 then (if i.val < 410 then (if i.val < 408 then (155 / 351)
    else (if i.val < 409 then (155 / 351) else 0)) else 0) else 0) else 0) else 0) else (if
    i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val < 461 then (if i.val <
    459 then 0 else (if i.val < 460 then 0 else (206 / 5967))) else (if i.val < 462 then (206 /
    5967) else (if i.val < 463 then (206 / 5967) else (-23 / 195)))) else (if i.val < 467 then
    (if i.val < 465 then (-23 / 195) else (if i.val < 466 then (-23 / 195) else (-23 / 390)))
    else (if i.val < 468 then (206 / 5967) else (if i.val < 469 then (-23 / 195) else (206 /
    5967))))) else 0) else (if i.val < 496 then (if i.val < 489 then 0 else (if i.val < 492 then
    0 else (if i.val < 494 then 0 else (if i.val < 495 then (328 / 1989) else 0)))) else 0)))
    else (if i.val < 560 then (if i.val < 534 then (if i.val < 521 then (if i.val < 515 then 0
    else (if i.val < 518 then 0 else (if i.val < 519 then 0 else (if i.val < 520 then (-7 /
    2808) else (-31 / 1404))))) else 0) else 0) else 0)) else (if i.val < 713 then (if i.val <
    662 then 0 else (if i.val < 687 then (if i.val < 674 then 0 else (if i.val < 680 then 0 else
    (if i.val < 683 then 0 else (if i.val < 685 then (if i.val < 684 then (31 / 1404) else 0)
    else 0)))) else 0)) else (if i.val < 764 then (if i.val < 738 then 0 else (if i.val < 751
    then (if i.val < 744 then 0 else (if i.val < 747 then (if i.val < 745 then 0 else (if i.val
    < 746 then 0 else (31 / 1404))) else (if i.val < 749 then (if i.val < 748 then (31 / 1404)
    else (7 / 2808)) else (7 / 2808)))) else (if i.val < 757 then (if i.val < 754 then (-749 /
    14040) else (if i.val < 755 then (-749 / 14040) else (-101 / 477360))) else (if i.val < 760
    then (if i.val < 758 then (-101 / 477360) else (if i.val < 759 then (-101 / 477360) else (-3
    / 1040))) else (if i.val < 762 then (-3 / 1040) else (if i.val < 763 then (-3 / 1040) else
    0)))))) else (if i.val < 789 then 0 else (if i.val < 802 then 0 else (if i.val < 808 then 0
    else (if i.val < 811 then (if i.val < 809 then 0 else (if i.val < 810 then 0 else (-1 /
    56160))) else 0))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high16Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (19, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (0, 0), (85, -1), (0, 0), (0, 0), (61, -1), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (88, -1), (0, 0), (0, 0), (111, 1), (0, 0), (201, (-155 / 351)),
    (0, 0), (0, 0), (204, (-70 / 351)), (0, 0), (0, 0), (0, 0), (206, (328 / 1989)), (207, (-155
    / 351)), (0, 0), (209, (-70 / 351)), (0, 0), (0, 0), (0, 0), (211, (328 / 1989)), (212,
    (-155 / 351)), (0, 0), (214, (-70 / 351)), (0, 0), (0, 0), (0, 0), (0, 0), (217, (328 /
    1989)), (218, (-155 / 351)), (219, (-70 / 351)), (0, 0), (0, 0), (406, (155 / 351)), (407,
    (155 / 351)), (388, (155 / 351)), (389, (155 / 351)), (408, (155 / 351)), (460, (206 /
    5967)), (461, (206 / 5967)), (462, (206 / 5967)), (463, (-23 / 195)), (464, (-23 / 195)),
    (465, (-23 / 195)), (466, (-23 / 390)), (467, (206 / 5967)), (468, (-23 / 195)), (469, (206
    / 5967)), (0, 0), (494, (328 / 1989)), (0, 0), (519, (-7 / 2808)), (520, (-31 / 1404)), (0,
    0), (0, 0), (0, 0), (746, (31 / 1404)), (683, (31 / 1404)), (747, (31 / 1404)), (748, (7 /
    2808)), (749, (7 / 2808)), (750, (7 / 2808)), (751, (-749 / 14040)), (752, (-749 / 14040)),
    (753, (-749 / 14040)), (754, (-749 / 14040)), (755, (-101 / 477360)), (756, (-101 /
    477360)), (757, (-101 / 477360)), (758, (-101 / 477360)), (759, (-3 / 1040)), (760, (-3 /
    1040)), (761, (-3 / 1040)), (762, (-3 / 1040)), (810, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high16Records_checked : imageRecords
    L24HighPsi.destination112 GenusTwoPsiPullbacksReplay.squareThreeClaim = high16Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high16_checked : L24HighPsi.correctionCoordinates 16 = high16 := by
  change imageCoordinates L24HighPsi.destination112
    GenusTwoPsiPullbacksReplay.squareThreeClaim = _
  rw [imageCoordinates_eq_records, high16Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high17 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then 0 else (if i.val < 21 then
    (if i.val < 19 then 0 else (if i.val < 20 then 0 else 1)) else 0))) else 0) else (if i.val <
    75 then (if i.val < 62 then (if i.val < 56 then 0 else (if i.val < 59 then 0 else (if i.val
    < 60 then 0 else (if i.val < 61 then 0 else -3)))) else 0) else (if i.val < 88 then (if
    i.val < 81 then 0 else (if i.val < 84 then (if i.val < 82 then 0 else (if i.val < 83 then -1
    else 0)) else (if i.val < 86 then (if i.val < 85 then -1 else 0) else 0))) else (if i.val <
    94 then (if i.val < 91 then (if i.val < 89 then -3 else 0) else 0) else 0)))) else (if i.val
    < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else (if i.val <
    110 then 0 else (if i.val < 111 then 0 else (if i.val < 112 then 3 else 0)))) else 0) else
    0) else (if i.val < 177 then 0 else (if i.val < 190 then 0 else (if i.val < 196 then 0 else
    (if i.val < 199 then 0 else (if i.val < 201 then 0 else (161 / 90)))))))) else (if i.val <
    305 then (if i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then
    (if i.val < 206 then (if i.val < 204 then 0 else (if i.val < 205 then (-40 / 9) else 0))
    else (if i.val < 207 then (206 / 51) else (161 / 90))) else (if i.val < 212 then (if i.val <
    210 then (-40 / 9) else (if i.val < 211 then (407 / 180) else (-7 / 36))) else (if i.val <
    213 then (407 / 180) else (if i.val < 214 then 0 else (-7 / 36))))) else (if i.val < 221
    then (if i.val < 218 then (if i.val < 216 then (407 / 180) else (if i.val < 217 then 0 else
    (-7 / 36))) else (if i.val < 219 then (407 / 180) else (if i.val < 220 then (-7 / 36) else
    0))) else 0)) else 0) else 0) else (if i.val < 356 then 0 else (if i.val < 381 then 0 else
    (if i.val < 394 then (if i.val < 387 then 0 else (if i.val < 390 then (if i.val < 388 then 0
    else (-25 / 9)) else 0)) else (if i.val < 400 then 0 else (if i.val < 403 then 0 else (if
    i.val < 405 then (if i.val < 404 then 0 else (-161 / 90)) else (if i.val < 406 then (-407 /
    180) else (-161 / 90)))))))))) else (if i.val < 611 then (if i.val < 509 then (if i.val <
    458 then (if i.val < 432 then (if i.val < 419 then (if i.val < 413 then (if i.val < 410 then
    (if i.val < 408 then (-407 / 180) else (if i.val < 409 then (-25 / 9) else 0)) else 0) else
    0) else 0) else 0) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if
    i.val < 461 then (if i.val < 459 then 0 else (if i.val < 460 then 0 else (62 / 153))) else
    (-19 / 90)) else (if i.val < 467 then (if i.val < 465 then (-19 / 90) else (if i.val < 466
    then (-13 / 15) else (-13 / 30))) else (if i.val < 468 then (-19 / 90) else (if i.val < 469
    then (-19 / 90) else (7 / 18))))) else 0) else (if i.val < 496 then (if i.val < 489 then 0
    else (if i.val < 492 then 0 else (if i.val < 494 then 0 else (if i.val < 495 then (206 / 51)
    else 0)))) else 0))) else (if i.val < 560 then (if i.val < 534 then (if i.val < 521 then (if
    i.val < 515 then 0 else (if i.val < 518 then 0 else (if i.val < 519 then 0 else (if i.val <
    520 then (-7 / 36) else (67 / 720))))) else (if i.val < 527 then (if i.val < 524 then (if
    i.val < 522 then (67 / 720) else 0) else 0) else 0)) else 0) else 0)) else (if i.val < 713
    then (if i.val < 662 then 0 else (if i.val < 687 then (if i.val < 674 then 0 else (if i.val
    < 680 then 0 else (if i.val < 683 then 0 else (if i.val < 685 then (if i.val < 684 then (-11
    / 72) else 0) else 0)))) else 0)) else (if i.val < 764 then (if i.val < 738 then 0 else (if
    i.val < 751 then (if i.val < 744 then 0 else (if i.val < 747 then (if i.val < 745 then 0
    else (-67 / 720)) else (if i.val < 749 then (if i.val < 748 then (-11 / 72) else (7 / 36))
    else (-1 / 40)))) else (if i.val < 757 then (if i.val < 754 then (if i.val < 752 then (-1 /
    40) else (if i.val < 753 then (-1 / 40) else (-37 / 90))) else (if i.val < 755 then (-37 /
    90) else (473 / 12240))) else (if i.val < 760 then (-1 / 180) else (if i.val < 762 then (if
    i.val < 761 then (-1 / 180) else (-37 / 720)) else (if i.val < 763 then (-37 / 720) else
    0)))))) else (if i.val < 789 then 0 else (if i.val < 802 then 0 else (if i.val < 808 then 0
    else (if i.val < 811 then (if i.val < 809 then 0 else (if i.val < 810 then 0 else (-1 /
    720))) else 0))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high17Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (20, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (82, -1), (0, 0), (0, 0), (84, -1), (0, 0), (0, 0), (0, 0), (61, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (88, -3), (0, 0), (0, 0), (111, 3), (0, 0), (201, (161 /
    90)), (202, (161 / 90)), (0, 0), (204, (-40 / 9)), (0, 0), (0, 0), (0, 0), (206, (206 /
    51)), (207, (161 / 90)), (208, (161 / 90)), (209, (-40 / 9)), (0, 0), (0, 0), (210, (407 /
    180)), (211, (-7 / 36)), (212, (407 / 180)), (0, 0), (214, (-7 / 36)), (0, 0), (0, 0), (215,
    (407 / 180)), (0, 0), (217, (-7 / 36)), (218, (407 / 180)), (219, (-7 / 36)), (404, (-161 /
    90)), (405, (-407 / 180)), (406, (-161 / 90)), (407, (-407 / 180)), (388, (-25 / 9)), (389,
    (-25 / 9)), (408, (-25 / 9)), (460, (62 / 153)), (461, (-19 / 90)), (462, (-19 / 90)), (463,
    (-19 / 90)), (464, (-19 / 90)), (465, (-13 / 15)), (466, (-13 / 30)), (467, (-19 / 90)),
    (468, (-19 / 90)), (469, (7 / 18)), (0, 0), (494, (206 / 51)), (0, 0), (519, (-7 / 36)),
    (520, (67 / 720)), (521, (67 / 720)), (0, 0), (745, (-67 / 720)), (746, (-67 / 720)), (683,
    (-11 / 72)), (747, (-11 / 72)), (748, (7 / 36)), (749, (-1 / 40)), (750, (-1 / 40)), (751,
    (-1 / 40)), (752, (-1 / 40)), (753, (-37 / 90)), (754, (-37 / 90)), (755, (473 / 12240)),
    (756, (473 / 12240)), (757, (-1 / 180)), (758, (-1 / 180)), (759, (-1 / 180)), (760, (-1 /
    180)), (761, (-37 / 720)), (762, (-37 / 720)), (810, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high17Records_checked : imageRecords
    L24HighPsi.destination113 GenusTwoPsiPullbacksReplay.productThreeClaim = high17Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high17_checked : L24HighPsi.correctionCoordinates 17 = high17 := by
  change imageCoordinates L24HighPsi.destination113
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high17Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high18 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then 0 else (if i.val < 21 then 0
    else (if i.val < 23 then (if i.val < 22 then 1 else 0) else 0)))) else 0) else (if i.val <
    75 then (if i.val < 62 then 0 else (if i.val < 68 then (if i.val < 65 then (if i.val < 63
    then -1 else 0) else 0) else 0)) else (if i.val < 88 then (if i.val < 81 then 0 else (if
    i.val < 84 then (if i.val < 82 then 0 else (if i.val < 83 then -1 else 0)) else (if i.val <
    86 then (if i.val < 85 then 0 else -3) else 0))) else (if i.val < 94 then (if i.val < 91
    then (if i.val < 89 then -3 else 0) else 0) else 0)))) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then 0 else (if i.val < 119 then (if i.val < 116 then 0 else (if
    i.val < 117 then 0 else (if i.val < 118 then 0 else 3))) else 0)) else 0) else (if i.val <
    177 then 0 else (if i.val < 190 then 0 else (if i.val < 196 then 0 else (if i.val < 199 then
    0 else (if i.val < 201 then 0 else (if i.val < 202 then (161 / 90) else 0)))))))) else (if
    i.val < 305 then (if i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val <
    209 then (if i.val < 206 then (if i.val < 204 then (161 / 90) else (if i.val < 205 then (-40
    / 9) else (407 / 180))) else (if i.val < 207 then (-7 / 36) else (if i.val < 208 then (407 /
    180) else 0))) else (if i.val < 212 then (if i.val < 210 then (-7 / 36) else (if i.val < 211
    then 0 else (206 / 51))) else (if i.val < 213 then (161 / 90) else (if i.val < 214 then (161
    / 90) else (-40 / 9))))) else (if i.val < 221 then (if i.val < 218 then (if i.val < 216 then
    0 else (if i.val < 217 then (407 / 180) else (-7 / 36))) else (if i.val < 219 then (407 /
    180) else (if i.val < 220 then (-7 / 36) else 0))) else 0)) else 0) else 0) else (if i.val <
    356 then 0 else (if i.val < 381 then 0 else (if i.val < 394 then (if i.val < 387 then 0 else
    (if i.val < 390 then (if i.val < 388 then 0 else (if i.val < 389 then (-161 / 90) else (-407
    / 180))) else 0)) else (if i.val < 400 then 0 else (if i.val < 403 then 0 else (if i.val <
    405 then (if i.val < 404 then 0 else (-161 / 90)) else (if i.val < 406 then (-407 / 180)
    else (-25 / 9)))))))))) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then
    (if i.val < 432 then (if i.val < 419 then (if i.val < 413 then (if i.val < 410 then (if
    i.val < 408 then (-25 / 9) else (if i.val < 409 then (-25 / 9) else 0)) else 0) else 0) else
    0) else 0) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
    461 then (if i.val < 459 then 0 else (if i.val < 460 then 0 else (-19 / 90))) else (if i.val
    < 462 then (62 / 153) else (-19 / 90))) else (if i.val < 467 then (if i.val < 465 then (-13
    / 15) else (if i.val < 466 then (-19 / 90) else (-13 / 30))) else (if i.val < 468 then (7 /
    18) else (-19 / 90)))) else 0) else (if i.val < 496 then (if i.val < 489 then 0 else (if
    i.val < 492 then 0 else (if i.val < 494 then 0 else (if i.val < 495 then (206 / 51) else
    0)))) else 0))) else (if i.val < 560 then (if i.val < 534 then (if i.val < 521 then (if
    i.val < 515 then 0 else (if i.val < 518 then 0 else (if i.val < 519 then 0 else (if i.val <
    520 then (-7 / 36) else (67 / 720))))) else (if i.val < 527 then (if i.val < 524 then (if
    i.val < 522 then 0 else (if i.val < 523 then (67 / 720) else 0)) else 0) else 0)) else 0)
    else 0)) else (if i.val < 713 then (if i.val < 662 then 0 else (if i.val < 687 then (if
    i.val < 674 then 0 else (if i.val < 680 then 0 else (if i.val < 683 then 0 else (if i.val <
    685 then (if i.val < 684 then (-67 / 720) else 0) else 0)))) else 0)) else (if i.val < 764
    then (if i.val < 738 then 0 else (if i.val < 751 then (if i.val < 744 then 0 else (if i.val
    < 747 then (if i.val < 745 then 0 else (if i.val < 746 then (-67 / 720) else (-11 / 72)))
    else (if i.val < 749 then (if i.val < 748 then (-11 / 72) else (-1 / 40)) else (if i.val <
    750 then (7 / 36) else (-1 / 40))))) else (if i.val < 757 then (if i.val < 754 then (if
    i.val < 752 then (-1 / 40) else (if i.val < 753 then (-37 / 90) else (-1 / 40))) else (if
    i.val < 755 then (-37 / 90) else (if i.val < 756 then (473 / 12240) else (-1 / 180)))) else
    (if i.val < 760 then (if i.val < 758 then (473 / 12240) else (-1 / 180)) else (if i.val <
    762 then (if i.val < 761 then (-37 / 720) else (-1 / 180)) else (if i.val < 763 then (-37 /
    720) else 0)))))) else (if i.val < 789 then 0 else (if i.val < 802 then 0 else (if i.val <
    808 then 0 else (if i.val < 811 then (if i.val < 809 then 0 else (if i.val < 810 then 0 else
    (-1 / 720))) else 0))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high18Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (21, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (82, -1), (0, 0), (0, 0), (62, -1), (0, 0), (0, 0), (0, 0), (85, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (88, -3), (0, 0), (0, 0), (118, 3), (0, 0), (201, (161 /
    90)), (203, (161 / 90)), (0, 0), (204, (-40 / 9)), (0, 0), (0, 0), (0, 0), (211, (206 /
    51)), (212, (161 / 90)), (213, (161 / 90)), (214, (-40 / 9)), (0, 0), (0, 0), (205, (407 /
    180)), (206, (-7 / 36)), (207, (407 / 180)), (0, 0), (209, (-7 / 36)), (0, 0), (0, 0), (216,
    (407 / 180)), (0, 0), (217, (-7 / 36)), (218, (407 / 180)), (219, (-7 / 36)), (404, (-161 /
    90)), (405, (-407 / 180)), (388, (-161 / 90)), (389, (-407 / 180)), (406, (-25 / 9)), (407,
    (-25 / 9)), (408, (-25 / 9)), (461, (62 / 153)), (460, (-19 / 90)), (462, (-19 / 90)), (463,
    (-19 / 90)), (465, (-19 / 90)), (464, (-13 / 15)), (466, (-13 / 30)), (469, (-19 / 90)),
    (468, (-19 / 90)), (467, (7 / 18)), (0, 0), (494, (206 / 51)), (0, 0), (519, (-7 / 36)),
    (520, (67 / 720)), (522, (67 / 720)), (0, 0), (745, (-67 / 720)), (683, (-67 / 720)), (746,
    (-11 / 72)), (747, (-11 / 72)), (749, (7 / 36)), (748, (-1 / 40)), (750, (-1 / 40)), (751,
    (-1 / 40)), (753, (-1 / 40)), (752, (-37 / 90)), (754, (-37 / 90)), (755, (473 / 12240)),
    (757, (473 / 12240)), (756, (-1 / 180)), (758, (-1 / 180)), (759, (-1 / 180)), (761, (-1 /
    180)), (760, (-37 / 720)), (762, (-37 / 720)), (810, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high18Records_checked : imageRecords
    L24HighPsi.destination114 GenusTwoPsiPullbacksReplay.productThreeClaim = high18Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high18_checked : L24HighPsi.correctionCoordinates 18 = high18 := by
  change imageCoordinates L24HighPsi.destination114
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high18Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high19 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then 0 else (if i.val < 18 then 0 else (if i.val < 21 then 0
    else (if i.val < 23 then (if i.val < 22 then 0 else 1) else 0)))) else 0) else (if i.val <
    75 then (if i.val < 62 then 0 else (if i.val < 68 then (if i.val < 65 then (if i.val < 63
    then -1 else 0) else 0) else 0)) else (if i.val < 88 then (if i.val < 81 then 0 else (if
    i.val < 84 then (if i.val < 82 then 0 else (if i.val < 83 then 0 else -3)) else (if i.val <
    86 then (if i.val < 85 then -1 else 0) else 0))) else (if i.val < 94 then (if i.val < 91
    then (if i.val < 89 then -3 else 0) else 0) else 0)))) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then 0 else (if i.val < 119 then (if i.val < 116 then 0 else (if
    i.val < 117 then 0 else (if i.val < 118 then 3 else 0))) else 0)) else 0) else (if i.val <
    177 then 0 else (if i.val < 190 then 0 else (if i.val < 196 then 0 else (if i.val < 199 then
    0 else (if i.val < 201 then 0 else (if i.val < 202 then 0 else (161 / 90))))))))) else (if
    i.val < 305 then (if i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val <
    209 then (if i.val < 206 then (if i.val < 204 then (161 / 90) else (if i.val < 205 then (-40
    / 9) else (407 / 180))) else (if i.val < 207 then (-7 / 36) else (if i.val < 208 then 0 else
    (407 / 180)))) else (if i.val < 212 then (if i.val < 210 then (-7 / 36) else (if i.val < 211
    then (407 / 180) else (-7 / 36))) else (if i.val < 213 then 0 else (if i.val < 214 then (407
    / 180) else (-7 / 36))))) else (if i.val < 221 then (if i.val < 218 then (if i.val < 216
    then (161 / 90) else (if i.val < 217 then (161 / 90) else (-40 / 9))) else (if i.val < 219
    then 0 else (if i.val < 220 then (206 / 51) else 0))) else 0)) else 0) else 0) else (if
    i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val < 394 then (if i.val < 387
    then 0 else (if i.val < 390 then (if i.val < 388 then 0 else (if i.val < 389 then (-161 /
    90) else (-407 / 180))) else 0)) else (if i.val < 400 then 0 else (if i.val < 403 then 0
    else (if i.val < 405 then (if i.val < 404 then 0 else (-25 / 9)) else (if i.val < 406 then
    (-25 / 9) else (-161 / 90)))))))))) else (if i.val < 611 then (if i.val < 509 then (if i.val
    < 458 then (if i.val < 432 then (if i.val < 419 then (if i.val < 413 then (if i.val < 410
    then (if i.val < 408 then (-407 / 180) else (if i.val < 409 then (-25 / 9) else 0)) else 0)
    else 0) else 0) else 0) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then
    (if i.val < 461 then (if i.val < 459 then 0 else (if i.val < 460 then 0 else (-19 / 90)))
    else (if i.val < 462 then (-19 / 90) else (if i.val < 463 then (-13 / 15) else (62 / 153))))
    else (if i.val < 467 then (if i.val < 465 then (-19 / 90) else (if i.val < 466 then (-19 /
    90) else (-13 / 30))) else (if i.val < 468 then (-19 / 90) else (if i.val < 469 then (7 /
    18) else (-19 / 90))))) else 0) else (if i.val < 496 then (if i.val < 489 then 0 else (if
    i.val < 492 then 0 else (if i.val < 494 then 0 else (if i.val < 495 then (206 / 51) else
    0)))) else 0))) else (if i.val < 560 then (if i.val < 534 then (if i.val < 521 then (if
    i.val < 515 then 0 else (if i.val < 518 then 0 else (if i.val < 519 then 0 else (if i.val <
    520 then (-7 / 36) else 0)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
    then (67 / 720) else (if i.val < 523 then (67 / 720) else 0)) else 0) else 0)) else 0) else
    0)) else (if i.val < 713 then (if i.val < 662 then 0 else (if i.val < 687 then (if i.val <
    674 then 0 else (if i.val < 680 then 0 else (if i.val < 683 then 0 else (if i.val < 685 then
    (if i.val < 684 then (-67 / 720) else 0) else 0)))) else 0)) else (if i.val < 764 then (if
    i.val < 738 then 0 else (if i.val < 751 then (if i.val < 744 then 0 else (if i.val < 747
    then (if i.val < 745 then 0 else (if i.val < 746 then (-11 / 72) else (-67 / 720))) else (if
    i.val < 749 then (if i.val < 748 then (-11 / 72) else (-1 / 40)) else (if i.val < 750 then
    (-1 / 40) else (-37 / 90))))) else (if i.val < 757 then (if i.val < 754 then (if i.val < 752
    then (7 / 36) else (-1 / 40)) else (if i.val < 755 then (-37 / 90) else (if i.val < 756 then
    (473 / 12240) else (-1 / 180)))) else (if i.val < 760 then (if i.val < 758 then (-1 / 180)
    else (if i.val < 759 then (-37 / 720) else (473 / 12240))) else (if i.val < 762 then (-1 /
    180) else (if i.val < 763 then (-37 / 720) else 0)))))) else (if i.val < 789 then 0 else (if
    i.val < 802 then 0 else (if i.val < 808 then 0 else (if i.val < 811 then (if i.val < 809
    then 0 else (if i.val < 810 then 0 else (-1 / 720))) else 0))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high19Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (22, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (84, -1), (0, 0), (0, 0), (62, -1), (0, 0), (0, 0), (0, 0), (83, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (88, -3), (0, 0), (0, 0), (117, 3), (0, 0), (202, (161 /
    90)), (203, (161 / 90)), (0, 0), (204, (-40 / 9)), (0, 0), (0, 0), (0, 0), (219, (206 /
    51)), (215, (161 / 90)), (216, (161 / 90)), (217, (-40 / 9)), (0, 0), (0, 0), (205, (407 /
    180)), (206, (-7 / 36)), (208, (407 / 180)), (0, 0), (209, (-7 / 36)), (0, 0), (0, 0), (213,
    (407 / 180)), (0, 0), (214, (-7 / 36)), (210, (407 / 180)), (211, (-7 / 36)), (406, (-161 /
    90)), (407, (-407 / 180)), (388, (-161 / 90)), (389, (-407 / 180)), (404, (-25 / 9)), (405,
    (-25 / 9)), (408, (-25 / 9)), (463, (62 / 153)), (460, (-19 / 90)), (464, (-19 / 90)), (461,
    (-19 / 90)), (465, (-19 / 90)), (462, (-13 / 15)), (466, (-13 / 30)), (469, (-19 / 90)),
    (467, (-19 / 90)), (468, (7 / 18)), (0, 0), (494, (206 / 51)), (0, 0), (519, (-7 / 36)),
    (521, (67 / 720)), (522, (67 / 720)), (0, 0), (746, (-67 / 720)), (683, (-67 / 720)), (745,
    (-11 / 72)), (747, (-11 / 72)), (751, (7 / 36)), (748, (-1 / 40)), (752, (-1 / 40)), (749,
    (-1 / 40)), (753, (-1 / 40)), (750, (-37 / 90)), (754, (-37 / 90)), (755, (473 / 12240)),
    (759, (473 / 12240)), (756, (-1 / 180)), (760, (-1 / 180)), (757, (-1 / 180)), (761, (-1 /
    180)), (758, (-37 / 720)), (762, (-37 / 720)), (810, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high19Records_checked : imageRecords
    L24HighPsi.destination116 GenusTwoPsiPullbacksReplay.productThreeClaim = high19Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high19_checked : L24HighPsi.correctionCoordinates 19 = high19 := by
  change imageCoordinates L24HighPsi.destination116
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high19Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high20 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then (if i.val < 28 then 0 else
    (if i.val < 29 then 0 else (if i.val < 30 then 1 else 0))) else 0) else 0)) else (if i.val <
    75 then 0 else (if i.val < 88 then 0 else (if i.val < 94 then (if i.val < 91 then 0 else (if
    i.val < 92 then 0 else (if i.val < 93 then -1 else 0))) else 0)))) else 0) else (if i.val <
    305 then (if i.val < 254 then (if i.val < 228 then (if i.val < 215 then 0 else (if i.val <
    221 then 0 else (if i.val < 224 then (if i.val < 222 then 0 else (if i.val < 223 then 0 else
    (-155 / 351))) else (if i.val < 226 then (if i.val < 225 then 0 else (-70 / 351)) else 0))))
    else (if i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 0
    else (if i.val < 230 then 0 else (328 / 1989))) else (if i.val < 232 then (-155 / 351) else
    (if i.val < 233 then (-70 / 351) else 0))) else 0) else 0)) else 0) else 0)) else (if i.val
    < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419
    then (if i.val < 413 then (if i.val < 410 then (if i.val < 408 then 0 else (if i.val < 409
    then 0 else (155 / 351))) else 0) else 0) else 0) else 0) else (if i.val < 483 then (if
    i.val < 470 then 0 else (if i.val < 476 then (if i.val < 473 then (if i.val < 471 then (206
    / 5967) else (if i.val < 472 then (-23 / 195) else (-23 / 390))) else 0) else 0)) else (if
    i.val < 496 then (if i.val < 489 then 0 else (if i.val < 492 then 0 else (if i.val < 494
    then 0 else (if i.val < 495 then 0 else (328 / 1989))))) else 0))) else (if i.val < 560 then
    (if i.val < 534 then (if i.val < 521 then 0 else (if i.val < 527 then (if i.val < 524 then
    (if i.val < 522 then 0 else (if i.val < 523 then 0 else (-7 / 2808))) else 0) else (if i.val
    < 530 then (if i.val < 528 then (-31 / 1404) else 0) else 0))) else 0) else 0)) else (if
    i.val < 713 then 0 else (if i.val < 764 then (if i.val < 738 then 0 else (if i.val < 751
    then 0 else (if i.val < 757 then 0 else (if i.val < 760 then 0 else (if i.val < 762 then 0
    else (if i.val < 763 then 0 else (31 / 1404))))))) else (if i.val < 789 then (if i.val < 776
    then (if i.val < 770 then (if i.val < 767 then (if i.val < 765 then (7 / 2808) else (-749 /
    14040)) else (if i.val < 768 then (-101 / 477360) else (if i.val < 769 then (-101 / 477360)
    else (-3 / 1040)))) else (if i.val < 773 then (if i.val < 771 then (-3 / 1040) else 0) else
    0)) else 0) else (if i.val < 802 then 0 else (if i.val < 808 then 0 else (if i.val < 811
    then 0 else (if i.val < 813 then (if i.val < 812 then (-1 / 56160) else 0) else 0)))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high20Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (29, 1), (0, 0), (0, 0), (0, 0), (92, -1), (0, 0), (223,
    (-155 / 351)), (0, 0), (225, (-70 / 351)), (0, 0), (0, 0), (0, 0), (230, (328 / 1989)),
    (231, (-155 / 351)), (232, (-70 / 351)), (409, (155 / 351)), (470, (206 / 5967)), (471, (-23
    / 195)), (472, (-23 / 390)), (0, 0), (495, (328 / 1989)), (0, 0), (523, (-7 / 2808)), (527,
    (-31 / 1404)), (0, 0), (763, (31 / 1404)), (764, (7 / 2808)), (765, (-749 / 14040)), (766,
    (-749 / 14040)), (767, (-101 / 477360)), (768, (-101 / 477360)), (769, (-3 / 1040)), (770,
    (-3 / 1040)), (811, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high20Records_checked : imageRecords
    L24HighPsi.destination137 GenusTwoPsiPullbacksReplay.squareTwoClaim = high20Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high20_checked : L24HighPsi.correctionCoordinates 20 = high20 := by
  change imageCoordinates L24HighPsi.destination137
    GenusTwoPsiPullbacksReplay.squareTwoClaim = _
  rw [imageCoordinates_eq_records, high20Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high21 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then (if i.val < 28 then 0 else
    (if i.val < 29 then 0 else (if i.val < 30 then 0 else 1))) else 0) else 0)) else (if i.val <
    75 then 0 else (if i.val < 88 then 0 else (if i.val < 94 then (if i.val < 91 then 0 else (if
    i.val < 92 then 0 else (if i.val < 93 then -3 else 0))) else 0)))) else 0) else (if i.val <
    305 then (if i.val < 254 then (if i.val < 228 then (if i.val < 215 then 0 else (if i.val <
    221 then 0 else (if i.val < 224 then (if i.val < 222 then 0 else (if i.val < 223 then 0 else
    (161 / 90))) else (if i.val < 226 then (if i.val < 225 then (161 / 90) else (-40 / 9)) else
    0)))) else (if i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229
    then 0 else (if i.val < 230 then (407 / 180) else (-7 / 36))) else (if i.val < 232 then (407
    / 180) else (if i.val < 233 then (-7 / 36) else 0))) else 0) else 0)) else 0) else 0)) else
    (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if
    i.val < 419 then (if i.val < 413 then (if i.val < 410 then (if i.val < 408 then 0 else (if
    i.val < 409 then 0 else (-25 / 9))) else 0) else 0) else 0) else 0) else (if i.val < 483
    then (if i.val < 470 then 0 else (if i.val < 476 then (if i.val < 473 then (if i.val < 471
    then (-19 / 90) else (if i.val < 472 then (-19 / 90) else (-13 / 30))) else 0) else 0)) else
    (if i.val < 496 then (if i.val < 489 then 0 else (if i.val < 492 then 0 else (if i.val < 494
    then 0 else (if i.val < 495 then 0 else (206 / 51))))) else 0))) else (if i.val < 560 then
    (if i.val < 534 then (if i.val < 521 then 0 else (if i.val < 527 then (if i.val < 524 then
    (if i.val < 522 then 0 else (if i.val < 523 then 0 else (-7 / 36))) else 0) else (if i.val <
    530 then (if i.val < 528 then (67 / 720) else (if i.val < 529 then (67 / 720) else 0)) else
    0))) else 0) else 0)) else (if i.val < 713 then 0 else (if i.val < 764 then (if i.val < 738
    then 0 else (if i.val < 751 then 0 else (if i.val < 757 then 0 else (if i.val < 760 then 0
    else (if i.val < 762 then 0 else (if i.val < 763 then 0 else (-11 / 72))))))) else (if i.val
    < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
    then (-1 / 40) else (if i.val < 766 then (-1 / 40) else (-37 / 90))) else (if i.val < 768
    then (473 / 12240) else (-1 / 180))) else (if i.val < 773 then (if i.val < 771 then (-37 /
    720) else 0) else 0)) else 0) else (if i.val < 802 then 0 else (if i.val < 808 then 0 else
    (if i.val < 811 then 0 else (if i.val < 813 then (if i.val < 812 then (-1 / 720) else 0)
    else 0)))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high21Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (30, 1), (0, 0), (0, 0), (92, -3), (0, 0), (223, (161
    / 90)), (224, (161 / 90)), (225, (-40 / 9)), (0, 0), (0, 0), (229, (407 / 180)), (230, (-7 /
    36)), (231, (407 / 180)), (232, (-7 / 36)), (409, (-25 / 9)), (470, (-19 / 90)), (471, (-19
    / 90)), (472, (-13 / 30)), (0, 0), (495, (206 / 51)), (0, 0), (523, (-7 / 36)), (527, (67 /
    720)), (528, (67 / 720)), (763, (-11 / 72)), (764, (-1 / 40)), (765, (-1 / 40)), (766, (-37
    / 90)), (767, (473 / 12240)), (768, (-1 / 180)), (769, (-1 / 180)), (770, (-37 / 720)),
    (811, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high21Records_checked : imageRecords
    L24HighPsi.destination138 GenusTwoPsiProduct.requested = high21Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high21_checked : L24HighPsi.correctionCoordinates 21 = high21 := by
  change imageCoordinates L24HighPsi.destination138
    GenusTwoPsiProduct.requested = _
  rw [imageCoordinates_eq_records, high21Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high22 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then 0 else (if i.val < 34 then
    (if i.val < 32 then 1 else 0) else 0)) else 0)) else (if i.val < 75 then (if i.val < 62 then
    (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 0 else (if i.val < 52 then 0
    else -1)) else 0) else 0) else 0) else (if i.val < 88 then 0 else (if i.val < 94 then 0 else
    (if i.val < 97 then (if i.val < 95 then 0 else (if i.val < 96 then 0 else -1)) else (if
    i.val < 99 then (if i.val < 98 then -1 else 0) else 0)))))) else (if i.val < 152 then (if
    i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else (if i.val < 110 then (if
    i.val < 108 then 0 else (if i.val < 109 then 1 else 0)) else 0)) else 0) else 0) else 0))
    else (if i.val < 305 then (if i.val < 254 then (if i.val < 228 then 0 else (if i.val < 241
    then (if i.val < 234 then (if i.val < 231 then 0 else (if i.val < 232 then 0 else (if i.val
    < 233 then 0 else (-155 / 351)))) else (if i.val < 237 then (if i.val < 235 then 0 else (if
    i.val < 236 then (-70 / 351) else (328 / 1989))) else (if i.val < 239 then (if i.val < 238
    then (-155 / 351) else 0) else (if i.val < 240 then (-70 / 351) else 0)))) else (if i.val <
    247 then (if i.val < 244 then (if i.val < 242 then (328 / 1989) else (if i.val < 243 then
    (-155 / 351) else (-70 / 351))) else (if i.val < 245 then 0 else (if i.val < 246 then (328 /
    1989) else (-155 / 351)))) else (if i.val < 250 then (if i.val < 248 then (-70 / 351) else
    0) else 0)))) else 0) else (if i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val
    < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then (155 / 351) else
    (if i.val < 383 then (155 / 351) else 0)) else 0) else 0) else 0))))) else (if i.val < 611
    then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
    i.val < 413 then (if i.val < 410 then 0 else (if i.val < 411 then 0 else (if i.val < 412
    then 0 else (155 / 351)))) else (if i.val < 416 then (if i.val < 414 then (155 / 351) else
    (if i.val < 415 then (155 / 351) else 0)) else 0)) else 0) else 0) else (if i.val < 483 then
    (if i.val < 470 then 0 else (if i.val < 476 then (if i.val < 473 then 0 else (206 / 5967))
    else (if i.val < 479 then (-23 / 195) else (if i.val < 481 then (if i.val < 480 then (-23 /
    390) else (206 / 5967)) else (if i.val < 482 then (-23 / 195) else (206 / 5967)))))) else
    (if i.val < 496 then 0 else (if i.val < 502 then (if i.val < 499 then (if i.val < 497 then
    (328 / 1989) else 0) else 0) else 0)))) else (if i.val < 560 then (if i.val < 534 then (if
    i.val < 521 then 0 else (if i.val < 527 then 0 else (if i.val < 530 then (if i.val < 528
    then 0 else (if i.val < 529 then 0 else (-7 / 2808))) else (if i.val < 532 then (if i.val <
    531 then (-31 / 1404) else 0) else 0)))) else 0) else 0)) else (if i.val < 713 then (if
    i.val < 662 then 0 else (if i.val < 687 then (if i.val < 674 then (if i.val < 668 then (if
    i.val < 665 then (if i.val < 663 then 0 else (if i.val < 664 then 0 else (31 / 1404))) else
    0) else 0) else 0) else 0)) else (if i.val < 764 then 0 else (if i.val < 789 then (if i.val
    < 776 then (if i.val < 770 then 0 else (if i.val < 773 then (if i.val < 771 then 0 else (if
    i.val < 772 then 0 else (31 / 1404))) else (if i.val < 774 then (31 / 1404) else (7 /
    2808)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then (7 / 2808) else
    (-749 / 14040)) else (if i.val < 780 then (-749 / 14040) else (if i.val < 781 then (-749 /
    14040) else (-101 / 477360)))) else (if i.val < 785 then (-101 / 477360) else (-3 / 1040))))
    else (if i.val < 802 then 0 else (if i.val < 808 then 0 else (if i.val < 811 then 0 else (if
    i.val < 813 then (if i.val < 812 then 0 else (-1 / 56160)) else 0)))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high22Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (31, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (0, 0), (96, -1), (0, 0), (0, 0), (52, -1), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (97, -1), (0, 0), (0, 0), (108, 1), (0, 0), (233, (-155 / 351)),
    (0, 0), (0, 0), (235, (-70 / 351)), (0, 0), (0, 0), (0, 0), (236, (328 / 1989)), (237, (-155
    / 351)), (0, 0), (239, (-70 / 351)), (0, 0), (0, 0), (0, 0), (241, (328 / 1989)), (242,
    (-155 / 351)), (0, 0), (243, (-70 / 351)), (0, 0), (0, 0), (0, 0), (0, 0), (245, (328 /
    1989)), (246, (-155 / 351)), (247, (-70 / 351)), (0, 0), (0, 0), (412, (155 / 351)), (413,
    (155 / 351)), (381, (155 / 351)), (382, (155 / 351)), (414, (155 / 351)), (473, (206 /
    5967)), (474, (206 / 5967)), (475, (206 / 5967)), (476, (-23 / 195)), (477, (-23 / 195)),
    (478, (-23 / 195)), (479, (-23 / 390)), (480, (206 / 5967)), (481, (-23 / 195)), (482, (206
    / 5967)), (0, 0), (496, (328 / 1989)), (0, 0), (529, (-7 / 2808)), (530, (-31 / 1404)), (0,
    0), (0, 0), (0, 0), (772, (31 / 1404)), (664, (31 / 1404)), (773, (31 / 1404)), (774, (7 /
    2808)), (775, (7 / 2808)), (776, (7 / 2808)), (777, (-749 / 14040)), (778, (-749 / 14040)),
    (779, (-749 / 14040)), (780, (-749 / 14040)), (781, (-101 / 477360)), (782, (-101 /
    477360)), (783, (-101 / 477360)), (784, (-101 / 477360)), (785, (-3 / 1040)), (786, (-3 /
    1040)), (787, (-3 / 1040)), (788, (-3 / 1040)), (812, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high22Records_checked : imageRecords
    L24HighPsi.destination145 GenusTwoPsiPullbacksReplay.squareThreeClaim = high22Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high22_checked : L24HighPsi.correctionCoordinates 22 = high22 := by
  change imageCoordinates L24HighPsi.destination145
    GenusTwoPsiPullbacksReplay.squareThreeClaim = _
  rw [imageCoordinates_eq_records, high22Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high23 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then 0 else (if i.val < 34 then
    (if i.val < 32 then 0 else (if i.val < 33 then 1 else 0)) else 0)) else 0)) else (if i.val <
    75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 0
    else (if i.val < 52 then 0 else -3)) else 0) else 0) else 0) else (if i.val < 88 then 0 else
    (if i.val < 94 then (if i.val < 91 then 0 else (if i.val < 92 then 0 else (if i.val < 93
    then 0 else -1))) else (if i.val < 97 then (if i.val < 95 then 0 else (if i.val < 96 then -1
    else 0)) else (if i.val < 99 then (if i.val < 98 then -3 else 0) else 0)))))) else (if i.val
    < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then 0 else (if i.val <
    110 then (if i.val < 108 then 0 else (if i.val < 109 then 3 else 0)) else 0)) else 0) else
    0) else 0)) else (if i.val < 305 then (if i.val < 254 then (if i.val < 228 then 0 else (if
    i.val < 241 then (if i.val < 234 then (if i.val < 231 then 0 else (if i.val < 232 then 0
    else (if i.val < 233 then 0 else (161 / 90)))) else (if i.val < 237 then (if i.val < 235
    then (161 / 90) else (if i.val < 236 then (-40 / 9) else (206 / 51))) else (if i.val < 239
    then (161 / 90) else (if i.val < 240 then (-40 / 9) else (407 / 180))))) else (if i.val <
    247 then (if i.val < 244 then (if i.val < 242 then (-7 / 36) else (if i.val < 243 then (407
    / 180) else (-7 / 36))) else (if i.val < 245 then (407 / 180) else (if i.val < 246 then (-7
    / 36) else (407 / 180)))) else (if i.val < 250 then (if i.val < 248 then (-7 / 36) else 0)
    else 0)))) else 0) else (if i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val <
    394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then (-25 / 9) else (if
    i.val < 383 then (-25 / 9) else 0)) else 0) else 0) else 0))))) else (if i.val < 611 then
    (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
    i.val < 413 then (if i.val < 410 then 0 else (if i.val < 411 then (-161 / 90) else (if i.val
    < 412 then (-407 / 180) else (-161 / 90)))) else (if i.val < 416 then (if i.val < 414 then
    (-407 / 180) else (if i.val < 415 then (-25 / 9) else 0)) else 0)) else 0) else 0) else (if
    i.val < 483 then (if i.val < 470 then 0 else (if i.val < 476 then (if i.val < 473 then 0
    else (if i.val < 474 then (62 / 153) else (-19 / 90))) else (if i.val < 479 then (if i.val <
    477 then (-19 / 90) else (if i.val < 478 then (-19 / 90) else (-13 / 15))) else (if i.val <
    481 then (if i.val < 480 then (-13 / 30) else (-19 / 90)) else (if i.val < 482 then (-19 /
    90) else (7 / 18)))))) else (if i.val < 496 then 0 else (if i.val < 502 then (if i.val < 499
    then (if i.val < 497 then (206 / 51) else 0) else 0) else 0)))) else (if i.val < 560 then
    (if i.val < 534 then (if i.val < 521 then 0 else (if i.val < 527 then 0 else (if i.val < 530
    then (if i.val < 528 then 0 else (if i.val < 529 then 0 else (-7 / 36))) else (if i.val <
    532 then (67 / 720) else 0)))) else 0) else 0)) else (if i.val < 713 then (if i.val < 662
    then 0 else (if i.val < 687 then (if i.val < 674 then (if i.val < 668 then (if i.val < 665
    then (if i.val < 663 then 0 else (if i.val < 664 then 0 else (-11 / 72))) else 0) else 0)
    else 0) else 0)) else (if i.val < 764 then 0 else (if i.val < 789 then (if i.val < 776 then
    (if i.val < 770 then 0 else (if i.val < 773 then (if i.val < 771 then 0 else (-67 / 720))
    else (if i.val < 774 then (-11 / 72) else (if i.val < 775 then (7 / 36) else (-1 / 40)))))
    else (if i.val < 782 then (if i.val < 779 then (-1 / 40) else (if i.val < 780 then (-37 /
    90) else (if i.val < 781 then (-37 / 90) else (473 / 12240)))) else (if i.val < 785 then (if
    i.val < 783 then (473 / 12240) else (-1 / 180)) else (if i.val < 787 then (-1 / 180) else
    (-37 / 720))))) else (if i.val < 802 then 0 else (if i.val < 808 then 0 else (if i.val < 811
    then 0 else (if i.val < 813 then (if i.val < 812 then 0 else (-1 / 720)) else 0)))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high23Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (32, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (93, -1), (0, 0), (0, 0), (95, -1), (0, 0), (0, 0), (0, 0), (52, -3), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (97, -3), (0, 0), (0, 0), (108, 3), (0, 0), (233, (161 /
    90)), (234, (161 / 90)), (0, 0), (235, (-40 / 9)), (0, 0), (0, 0), (0, 0), (236, (206 /
    51)), (237, (161 / 90)), (238, (161 / 90)), (239, (-40 / 9)), (0, 0), (0, 0), (240, (407 /
    180)), (241, (-7 / 36)), (242, (407 / 180)), (0, 0), (243, (-7 / 36)), (0, 0), (0, 0), (244,
    (407 / 180)), (0, 0), (245, (-7 / 36)), (246, (407 / 180)), (247, (-7 / 36)), (410, (-161 /
    90)), (411, (-407 / 180)), (412, (-161 / 90)), (413, (-407 / 180)), (381, (-25 / 9)), (382,
    (-25 / 9)), (414, (-25 / 9)), (473, (62 / 153)), (474, (-19 / 90)), (475, (-19 / 90)), (476,
    (-19 / 90)), (477, (-19 / 90)), (478, (-13 / 15)), (479, (-13 / 30)), (480, (-19 / 90)),
    (481, (-19 / 90)), (482, (7 / 18)), (0, 0), (496, (206 / 51)), (0, 0), (529, (-7 / 36)),
    (530, (67 / 720)), (531, (67 / 720)), (0, 0), (771, (-67 / 720)), (772, (-67 / 720)), (664,
    (-11 / 72)), (773, (-11 / 72)), (774, (7 / 36)), (775, (-1 / 40)), (776, (-1 / 40)), (777,
    (-1 / 40)), (778, (-1 / 40)), (779, (-37 / 90)), (780, (-37 / 90)), (781, (473 / 12240)),
    (782, (473 / 12240)), (783, (-1 / 180)), (784, (-1 / 180)), (785, (-1 / 180)), (786, (-1 /
    180)), (787, (-37 / 720)), (788, (-37 / 720)), (812, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high23Records_checked : imageRecords
    L24HighPsi.destination146 GenusTwoPsiPullbacksReplay.productThreeClaim = high23Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high23_checked : L24HighPsi.correctionCoordinates 23 = high23 := by
  change imageCoordinates L24HighPsi.destination146
    GenusTwoPsiPullbacksReplay.productThreeClaim = _
  rw [imageCoordinates_eq_records, high23Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high24 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then (if i.val < 31 then 0 else (if i.val < 34 then
    (if i.val < 32 then 0 else (if i.val < 33 then 0 else 1)) else 0)) else 0)) else (if i.val <
    75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 0
    else (if i.val < 52 then 0 else -1)) else 0) else 0) else 0) else (if i.val < 88 then 0 else
    (if i.val < 94 then 0 else (if i.val < 97 then (if i.val < 95 then -1 else 0) else (if i.val
    < 99 then (if i.val < 98 then -1 else 0) else 0)))))) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then (if i.val < 107 then 0 else (if i.val < 110 then (if i.val <
    108 then 0 else (if i.val < 109 then 1 else 0)) else 0)) else 0) else 0) else 0)) else (if
    i.val < 305 then (if i.val < 254 then (if i.val < 228 then 0 else (if i.val < 241 then (if
    i.val < 234 then 0 else (if i.val < 237 then (if i.val < 235 then (-155 / 351) else (if
    i.val < 236 then (-70 / 351) else (328 / 1989))) else (if i.val < 239 then (if i.val < 238
    then 0 else (-155 / 351)) else (if i.val < 240 then (-70 / 351) else (-155 / 351))))) else
    (if i.val < 247 then (if i.val < 244 then (if i.val < 242 then (-70 / 351) else (if i.val <
    243 then 0 else (328 / 1989))) else (if i.val < 245 then (-155 / 351) else (if i.val < 246
    then (-70 / 351) else 0))) else (if i.val < 250 then (if i.val < 248 then (328 / 1989) else
    0) else 0)))) else 0) else (if i.val < 356 then 0 else (if i.val < 381 then 0 else (if i.val
    < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then (155 / 351) else
    (if i.val < 383 then (155 / 351) else 0)) else 0) else 0) else 0))))) else (if i.val < 611
    then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
    i.val < 413 then (if i.val < 410 then 0 else (if i.val < 411 then (155 / 351) else (if i.val
    < 412 then (155 / 351) else 0))) else (if i.val < 416 then (if i.val < 414 then 0 else (if
    i.val < 415 then (155 / 351) else 0)) else 0)) else 0) else 0) else (if i.val < 483 then (if
    i.val < 470 then 0 else (if i.val < 476 then (if i.val < 473 then 0 else (if i.val < 474
    then (206 / 5967) else (-23 / 195))) else (if i.val < 479 then (if i.val < 477 then (206 /
    5967) else (if i.val < 478 then (206 / 5967) else (-23 / 195))) else (if i.val < 481 then
    (if i.val < 480 then (-23 / 390) else (-23 / 195)) else (206 / 5967))))) else (if i.val <
    496 then 0 else (if i.val < 502 then (if i.val < 499 then (if i.val < 497 then (328 / 1989)
    else 0) else 0) else 0)))) else (if i.val < 560 then (if i.val < 534 then (if i.val < 521
    then 0 else (if i.val < 527 then 0 else (if i.val < 530 then (if i.val < 528 then 0 else (if
    i.val < 529 then 0 else (-7 / 2808))) else (if i.val < 532 then (if i.val < 531 then 0 else
    (-31 / 1404)) else 0)))) else 0) else 0)) else (if i.val < 713 then (if i.val < 662 then 0
    else (if i.val < 687 then (if i.val < 674 then (if i.val < 668 then (if i.val < 665 then (if
    i.val < 663 then 0 else (if i.val < 664 then 0 else (31 / 1404))) else 0) else 0) else 0)
    else 0)) else (if i.val < 764 then 0 else (if i.val < 789 then (if i.val < 776 then (if
    i.val < 770 then 0 else (if i.val < 773 then (if i.val < 771 then 0 else (if i.val < 772
    then (31 / 1404) else 0)) else (if i.val < 774 then (31 / 1404) else (if i.val < 775 then (7
    / 2808) else (-749 / 14040))))) else (if i.val < 782 then (if i.val < 779 then (if i.val <
    777 then (-749 / 14040) else (7 / 2808)) else (if i.val < 780 then (-749 / 14040) else (if
    i.val < 781 then (-749 / 14040) else (-101 / 477360)))) else (if i.val < 785 then (if i.val
    < 783 then (-101 / 477360) else (-3 / 1040)) else (if i.val < 787 then (-101 / 477360) else
    (-3 / 1040))))) else (if i.val < 802 then 0 else (if i.val < 808 then 0 else (if i.val < 811
    then 0 else (if i.val < 813 then (if i.val < 812 then 0 else (-1 / 56160)) else 0)))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high24Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (33, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (0, 0), (94, -1), (0, 0), (0, 0), (52, -1), (0, 0), (0, 0), (0,
    0), (0, 0), (0, 0), (0, 0), (97, -1), (0, 0), (0, 0), (108, 1), (0, 0), (234, (-155 / 351)),
    (0, 0), (0, 0), (235, (-70 / 351)), (0, 0), (0, 0), (0, 0), (236, (328 / 1989)), (238, (-155
    / 351)), (0, 0), (239, (-70 / 351)), (0, 0), (0, 0), (0, 0), (247, (328 / 1989)), (244,
    (-155 / 351)), (0, 0), (245, (-70 / 351)), (0, 0), (0, 0), (0, 0), (0, 0), (243, (328 /
    1989)), (240, (-155 / 351)), (241, (-70 / 351)), (0, 0), (0, 0), (410, (155 / 351)), (411,
    (155 / 351)), (381, (155 / 351)), (382, (155 / 351)), (414, (155 / 351)), (473, (206 /
    5967)), (476, (206 / 5967)), (477, (206 / 5967)), (474, (-23 / 195)), (475, (-23 / 195)),
    (478, (-23 / 195)), (479, (-23 / 390)), (481, (206 / 5967)), (480, (-23 / 195)), (482, (206
    / 5967)), (0, 0), (496, (328 / 1989)), (0, 0), (529, (-7 / 2808)), (531, (-31 / 1404)), (0,
    0), (0, 0), (0, 0), (771, (31 / 1404)), (664, (31 / 1404)), (773, (31 / 1404)), (774, (7 /
    2808)), (777, (7 / 2808)), (778, (7 / 2808)), (775, (-749 / 14040)), (776, (-749 / 14040)),
    (779, (-749 / 14040)), (780, (-749 / 14040)), (781, (-101 / 477360)), (782, (-101 /
    477360)), (785, (-101 / 477360)), (786, (-101 / 477360)), (783, (-3 / 1040)), (784, (-3 /
    1040)), (787, (-3 / 1040)), (788, (-3 / 1040)), (812, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high24Records_checked : imageRecords
    L24HighPsi.destination148 GenusTwoPsiPullbacksReplay.squareThreeClaim = high24Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high24_checked : L24HighPsi.correctionCoordinates 24 = high24 := by
  change imageCoordinates L24HighPsi.destination148
    GenusTwoPsiPullbacksReplay.squareThreeClaim = _
  rw [imageCoordinates_eq_records, high24Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high25 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then (if i.val < 40 then
    (if i.val < 38 then 1 else 0) else 0) else 0))) else 0) else (if i.val < 152 then (if i.val
    < 126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then (if i.val < 102
    then -1 else 0) else 0) else 0) else 0) else 0) else 0)) else (if i.val < 305 then (if i.val
    < 254 then (if i.val < 228 then 0 else (if i.val < 241 then 0 else (if i.val < 247 then 0
    else (if i.val < 250 then 0 else (if i.val < 252 then (if i.val < 251 then 0 else (-155 /
    351)) else (if i.val < 253 then 0 else (-70 / 351))))))) else (if i.val < 279 then (if i.val
    < 266 then (if i.val < 260 then (if i.val < 257 then 0 else (if i.val < 258 then (328 /
    1989) else (if i.val < 259 then (-155 / 351) else (-70 / 351)))) else 0) else 0) else 0))
    else 0)) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val < 432
    then (if i.val < 419 then (if i.val < 413 then 0 else (if i.val < 416 then (if i.val < 414
    then 0 else (if i.val < 415 then 0 else (155 / 351))) else 0)) else 0) else 0) else (if
    i.val < 483 then 0 else (if i.val < 496 then (if i.val < 489 then (if i.val < 486 then (if
    i.val < 484 then (206 / 5967) else (if i.val < 485 then (-23 / 195) else (-23 / 390))) else
    0) else 0) else (if i.val < 502 then (if i.val < 499 then (if i.val < 497 then 0 else (if
    i.val < 498 then (328 / 1989) else 0)) else 0) else 0)))) else (if i.val < 560 then (if
    i.val < 534 then (if i.val < 521 then 0 else (if i.val < 527 then 0 else (if i.val < 530
    then 0 else (if i.val < 532 then 0 else (if i.val < 533 then (-7 / 2808) else 0))))) else
    (if i.val < 547 then (if i.val < 540 then (if i.val < 537 then (if i.val < 535 then 0 else
    (if i.val < 536 then 0 else (-31 / 1404))) else 0) else 0) else 0)) else 0)) else (if i.val
    < 713 then 0 else (if i.val < 764 then 0 else (if i.val < 789 then 0 else (if i.val < 802
    then (if i.val < 795 then (if i.val < 792 then (if i.val < 790 then (31 / 1404) else (if
    i.val < 791 then (7 / 2808) else (-749 / 14040))) else (if i.val < 793 then (-749 / 14040)
    else (-101 / 477360))) else (if i.val < 798 then (if i.val < 796 then (-3 / 1040) else (if
    i.val < 797 then (-3 / 1040) else 0)) else 0)) else (if i.val < 808 then 0 else (if i.val <
    811 then 0 else (if i.val < 813 then 0 else (if i.val < 814 then (-1 / 56160) else
    0))))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high25Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (37, 1), (0, 0), (0, 0), (0, 0), (101, -1), (0, 0), (251,
    (-155 / 351)), (0, 0), (253, (-70 / 351)), (0, 0), (0, 0), (0, 0), (257, (328 / 1989)),
    (258, (-155 / 351)), (259, (-70 / 351)), (415, (155 / 351)), (483, (206 / 5967)), (484, (-23
    / 195)), (485, (-23 / 390)), (0, 0), (497, (328 / 1989)), (0, 0), (532, (-7 / 2808)), (536,
    (-31 / 1404)), (0, 0), (789, (31 / 1404)), (790, (7 / 2808)), (791, (-749 / 14040)), (792,
    (-749 / 14040)), (793, (-101 / 477360)), (794, (-101 / 477360)), (795, (-3 / 1040)), (796,
    (-3 / 1040)), (813, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high25Records_checked : imageRecords
    L24HighPsi.destination170 GenusTwoPsiPullbacksReplay.squareTwoClaim = high25Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high25_checked : L24HighPsi.correctionCoordinates 25 = high25 := by
  change imageCoordinates L24HighPsi.destination170
    GenusTwoPsiPullbacksReplay.squareTwoClaim = _
  rw [imageCoordinates_eq_records, high25Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high26 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then (if i.val < 40 then
    (if i.val < 38 then 0 else (if i.val < 39 then 1 else 0)) else 0) else 0))) else 0) else (if
    i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then (if i.val <
    104 then (if i.val < 102 then -3 else 0) else 0) else 0) else 0) else 0) else 0)) else (if
    i.val < 305 then (if i.val < 254 then (if i.val < 228 then 0 else (if i.val < 241 then 0
    else (if i.val < 247 then 0 else (if i.val < 250 then 0 else (if i.val < 252 then (if i.val
    < 251 then 0 else (161 / 90)) else (if i.val < 253 then (161 / 90) else (-40 / 9))))))) else
    (if i.val < 279 then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if
    i.val < 255 then 0 else (if i.val < 256 then 0 else (407 / 180))) else (if i.val < 258 then
    (-7 / 36) else (if i.val < 259 then (407 / 180) else (-7 / 36)))) else 0) else 0) else 0))
    else 0)) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val < 432
    then (if i.val < 419 then (if i.val < 413 then 0 else (if i.val < 416 then (if i.val < 414
    then 0 else (if i.val < 415 then 0 else (-25 / 9))) else 0)) else 0) else 0) else (if i.val
    < 483 then 0 else (if i.val < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val <
    484 then (-19 / 90) else (if i.val < 485 then (-19 / 90) else (-13 / 30))) else 0) else 0)
    else (if i.val < 502 then (if i.val < 499 then (if i.val < 497 then 0 else (if i.val < 498
    then (206 / 51) else 0)) else 0) else 0)))) else (if i.val < 560 then (if i.val < 534 then
    (if i.val < 521 then 0 else (if i.val < 527 then 0 else (if i.val < 530 then 0 else (if
    i.val < 532 then 0 else (if i.val < 533 then (-7 / 36) else 0))))) else (if i.val < 547 then
    (if i.val < 540 then (if i.val < 537 then (if i.val < 535 then 0 else (if i.val < 536 then 0
    else (67 / 720))) else (if i.val < 538 then (67 / 720) else 0)) else 0) else 0)) else 0))
    else (if i.val < 713 then 0 else (if i.val < 764 then 0 else (if i.val < 789 then 0 else (if
    i.val < 802 then (if i.val < 795 then (if i.val < 792 then (if i.val < 790 then (-11 / 72)
    else (-1 / 40)) else (if i.val < 793 then (-37 / 90) else (if i.val < 794 then (473 / 12240)
    else (-1 / 180)))) else (if i.val < 798 then (if i.val < 796 then (-1 / 180) else (if i.val
    < 797 then (-37 / 720) else 0)) else 0)) else (if i.val < 808 then 0 else (if i.val < 811
    then 0 else (if i.val < 813 then 0 else (if i.val < 814 then (-1 / 720) else 0))))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high26Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (38, 1), (0, 0), (0, 0), (101, -3), (0, 0), (251,
    (161 / 90)), (252, (161 / 90)), (253, (-40 / 9)), (0, 0), (0, 0), (256, (407 / 180)), (257,
    (-7 / 36)), (258, (407 / 180)), (259, (-7 / 36)), (415, (-25 / 9)), (483, (-19 / 90)), (484,
    (-19 / 90)), (485, (-13 / 30)), (0, 0), (497, (206 / 51)), (0, 0), (532, (-7 / 36)), (536,
    (67 / 720)), (537, (67 / 720)), (789, (-11 / 72)), (790, (-1 / 40)), (791, (-1 / 40)), (792,
    (-37 / 90)), (793, (473 / 12240)), (794, (-1 / 180)), (795, (-1 / 180)), (796, (-37 / 720)),
    (813, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high26Records_checked : imageRecords
    L24HighPsi.destination171 GenusTwoPsiProduct.requested = high26Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high26_checked : L24HighPsi.correctionCoordinates 26 = high26 := by
  change imageCoordinates L24HighPsi.destination171
    GenusTwoPsiProduct.requested = _
  rw [imageCoordinates_eq_records, high26Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high27 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then (if i.val < 40 then 0
    else (if i.val < 41 then 0 else (if i.val < 42 then 0 else 1))) else 0))) else 0) else (if
    i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then (if i.val <
    104 then 0 else (if i.val < 105 then 0 else (if i.val < 106 then -1 else 0))) else 0) else
    0) else 0) else 0)) else (if i.val < 305 then (if i.val < 254 then 0 else (if i.val < 279
    then (if i.val < 266 then (if i.val < 260 then 0 else (if i.val < 263 then 0 else (if i.val
    < 264 then (-155 / 351) else (if i.val < 265 then 0 else (-70 / 351))))) else (if i.val <
    272 then (if i.val < 269 then 0 else (if i.val < 270 then (328 / 1989) else (if i.val < 271
    then (-155 / 351) else (-70 / 351)))) else 0)) else 0)) else 0)) else (if i.val < 611 then
    (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
    i.val < 413 then 0 else (if i.val < 416 then 0 else (if i.val < 417 then (155 / 351) else
    0))) else 0) else 0) else (if i.val < 483 then 0 else (if i.val < 496 then (if i.val < 489
    then (if i.val < 486 then 0 else (if i.val < 487 then (206 / 5967) else (if i.val < 488 then
    (-23 / 195) else (-23 / 390)))) else 0) else (if i.val < 502 then (if i.val < 499 then (if
    i.val < 497 then 0 else (if i.val < 498 then 0 else (328 / 1989))) else 0) else 0)))) else
    (if i.val < 560 then (if i.val < 534 then 0 else (if i.val < 547 then (if i.val < 540 then
    (if i.val < 537 then 0 else (if i.val < 538 then 0 else (if i.val < 539 then (-7 / 2808)
    else 0))) else (if i.val < 543 then (if i.val < 541 then 0 else (if i.val < 542 then 0 else
    (-31 / 1404))) else 0)) else 0)) else 0)) else (if i.val < 713 then 0 else (if i.val < 764
    then 0 else (if i.val < 789 then 0 else (if i.val < 802 then (if i.val < 795 then 0 else (if
    i.val < 798 then (if i.val < 796 then 0 else (if i.val < 797 then 0 else (31 / 1404))) else
    (if i.val < 800 then (if i.val < 799 then (7 / 2808) else (-749 / 14040)) else (if i.val <
    801 then (-749 / 14040) else (-101 / 477360))))) else (if i.val < 808 then (if i.val < 805
    then (if i.val < 803 then (-101 / 477360) else (-3 / 1040)) else 0) else (if i.val < 811
    then 0 else (if i.val < 813 then 0 else (if i.val < 814 then 0 else (-1 / 56160)))))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high27Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (42, 1), (0, 0), (0, 0), (0, 0), (105, -1), (0, 0), (263,
    (-155 / 351)), (0, 0), (265, (-70 / 351)), (0, 0), (0, 0), (0, 0), (269, (328 / 1989)),
    (270, (-155 / 351)), (271, (-70 / 351)), (416, (155 / 351)), (486, (206 / 5967)), (487, (-23
    / 195)), (488, (-23 / 390)), (0, 0), (498, (328 / 1989)), (0, 0), (538, (-7 / 2808)), (542,
    (-31 / 1404)), (0, 0), (797, (31 / 1404)), (798, (7 / 2808)), (799, (-749 / 14040)), (800,
    (-749 / 14040)), (801, (-101 / 477360)), (802, (-101 / 477360)), (803, (-3 / 1040)), (804,
    (-3 / 1040)), (814, (-1 / 56160))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high27Records_checked : imageRecords
    L24HighPsi.destination192 GenusTwoPsiPullbacksReplay.squareTwoClaim = high27Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high27_checked : L24HighPsi.correctionCoordinates 27 = high27 := by
  change imageCoordinates L24HighPsi.destination192
    GenusTwoPsiPullbacksReplay.squareTwoClaim = _
  rw [imageCoordinates_eq_records, high27Records_checked]
  decide +kernel

/-- Incoming exact raw coordinates; validity is checked separately. -/
def high28 : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then 0 else (if i.val < 46
    then (if i.val < 44 then 1 else 0) else 0)))) else 0) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then 0 else (if i.val <
    105 then 0 else (if i.val < 106 then -3 else 0))) else 0) else 0) else 0) else 0)) else (if
    i.val < 305 then (if i.val < 254 then 0 else (if i.val < 279 then (if i.val < 266 then (if
    i.val < 260 then 0 else (if i.val < 263 then 0 else (if i.val < 264 then (161 / 90) else (if
    i.val < 265 then (161 / 90) else (-40 / 9))))) else (if i.val < 272 then (if i.val < 269
    then (if i.val < 267 then 0 else (if i.val < 268 then 0 else (407 / 180))) else (if i.val <
    270 then (-7 / 36) else (if i.val < 271 then (407 / 180) else (-7 / 36)))) else 0)) else 0))
    else 0)) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val < 432
    then (if i.val < 419 then (if i.val < 413 then 0 else (if i.val < 416 then 0 else (if i.val
    < 417 then (-25 / 9) else 0))) else 0) else 0) else (if i.val < 483 then 0 else (if i.val <
    496 then (if i.val < 489 then (if i.val < 486 then 0 else (if i.val < 487 then (-19 / 90)
    else (if i.val < 488 then (-19 / 90) else (-13 / 30)))) else 0) else (if i.val < 502 then
    (if i.val < 499 then (if i.val < 497 then 0 else (if i.val < 498 then 0 else (206 / 51)))
    else 0) else 0)))) else (if i.val < 560 then (if i.val < 534 then 0 else (if i.val < 547
    then (if i.val < 540 then (if i.val < 537 then 0 else (if i.val < 538 then 0 else (if i.val
    < 539 then (-7 / 36) else 0))) else (if i.val < 543 then (if i.val < 541 then 0 else (if
    i.val < 542 then 0 else (67 / 720))) else (if i.val < 545 then (if i.val < 544 then (67 /
    720) else 0) else 0))) else 0)) else 0)) else (if i.val < 713 then 0 else (if i.val < 764
    then 0 else (if i.val < 789 then 0 else (if i.val < 802 then (if i.val < 795 then 0 else (if
    i.val < 798 then (if i.val < 796 then 0 else (if i.val < 797 then 0 else (-11 / 72))) else
    (if i.val < 800 then (-1 / 40) else (if i.val < 801 then (-37 / 90) else (473 / 12240)))))
    else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then (-1 / 180) else (if
    i.val < 804 then (-1 / 180) else (-37 / 720))) else 0) else (if i.val < 811 then 0 else (if
    i.val < 813 then 0 else (if i.val < 814 then 0 else (-1 / 720)))))))))))

/-- Untrusted ordered coefficient records; zero entries are retained. -/
def high28Records : List (Fin 815 × ℚ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (43, 1), (0, 0), (0, 0), (105, -3), (0, 0), (263,
    (161 / 90)), (264, (161 / 90)), (265, (-40 / 9)), (0, 0), (0, 0), (268, (407 / 180)), (269,
    (-7 / 36)), (270, (407 / 180)), (271, (-7 / 36)), (416, (-25 / 9)), (486, (-19 / 90)), (487,
    (-19 / 90)), (488, (-13 / 30)), (0, 0), (498, (206 / 51)), (0, 0), (538, (-7 / 36)), (542,
    (67 / 720)), (543, (67 / 720)), (797, (-11 / 72)), (798, (-1 / 40)), (799, (-1 / 40)), (800,
    (-37 / 90)), (801, (473 / 12240)), (802, (-1 / 180)), (803, (-1 / 180)), (804, (-37 / 720)),
    (814, (-1 / 720))]

/-- Every finite record is bound to the actual source and destination. -/
theorem high28Records_checked : imageRecords
    L24HighPsi.destination193 GenusTwoPsiProduct.requested = high28Records := by
  decide +kernel

/-- The full incoming row agrees with its actual contextual source image. -/
theorem high28_checked : L24HighPsi.correctionCoordinates 28 = high28 := by
  change imageCoordinates L24HighPsi.destination193
    GenusTwoPsiProduct.requested = _
  rw [imageCoordinates_eq_records, high28Records_checked]
  decide +kernel

/-- All checked incoming rows, in their retained source-operation order. -/
def highRows : Fin 29 → Coordinates 815 :=
  ![high0, high1, high2, high3, high4, high5, high6, high7, high8, high9, high10, high11,
    high12, high13, high14, high15, high16, high17, high18, high19, high20, high21, high22,
    high23, high24, high25, high26, high27, high28]

/-- Exact chosen rational weights; the final sum is checked below. -/
def highWeights : Fin 29 → ℚ :=
  ![(1 / 6), (-1 / 6), (-1 / 2), (1 / 2), (-1 / 6), (1 / 3), (-1 / 6), (-1 / 6), (1 / 3), (-1 /
    6), (-1 / 3), (2 / 3), (-1 / 2), (1 / 6), (1 / 2), (-1 / 6), (-1 / 2), (1 / 6), (1 / 2), (-1
    / 6), (-3 / 2), (3 / 2), (-1 / 6), (1 / 3), (-1 / 6), (-1 / 3), (2 / 3), (-1 / 3), (2 / 3)]

/-- Every row in this complete family has been replayed. -/
theorem high_checked (i : Fin 29) :
    L24HighPsi.correctionCoordinates i = highRows i := by
  fin_cases i
  · exact high0_checked
  · exact high1_checked
  · exact high2_checked
  · exact high3_checked
  · exact high4_checked
  · exact high5_checked
  · exact high6_checked
  · exact high7_checked
  · exact high8_checked
  · exact high9_checked
  · exact high10_checked
  · exact high11_checked
  · exact high12_checked
  · exact high13_checked
  · exact high14_checked
  · exact high15_checked
  · exact high16_checked
  · exact high17_checked
  · exact high18_checked
  · exact high19_checked
  · exact high20_checked
  · exact high21_checked
  · exact high22_checked
  · exact high23_checked
  · exact high24_checked
  · exact high25_checked
  · exact high26_checked
  · exact high27_checked
  · exact high28_checked

end AxiomaticGW.L24CorrectionsReplay
