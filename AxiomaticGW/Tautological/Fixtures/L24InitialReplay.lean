/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24InitialHints
public import AxiomaticGW.Tautological.StrataCoordinateRecords
public import AxiomaticGW.Tautological.Fixtures.L24CorrectionsReplay

/-!
# Exact BP initial coefficients and auxiliary cancellation

The proposed records retain all 306 signed terms for each of the four psi
contributions, including a zero marker for each justified dimension excess.
They must equal the actual Lean computation before arithmetic is used.
The final target is the unchanged, independently held initial L24 claim.
-/

@[expose] public section

namespace AxiomaticGW.L24InitialReplay
open RelationCertificate

set_option maxRecDepth 20000

set_option maxHeartbeats 800000 in
-- Elaborating the 306 exact records exceeds the default declaration budget.
/-- Proposed records for the psi-0 term; no multiplicity is removed. -/
def records0 : List (Fin 860 × ℚ) :=
  ([(48, -2), (54, -2), (89, -2), (48, -2), (54, -2), (89, -2), (57, -2), (830, -2), (98, -2),
    (64, -2), (832, -2), (102, -2), (57, -2), (830, -2), (98, -2), (64, -2), (832, -2), (102,
    -2), (0, 0), (14, 2), (44, 2), (0, 0), (14, 2), (44, 2), (0, 0), (14, 2), (44, 2), (0, 0),
    (14, 2), (44, 2), (0, 0), (14, 2), (44, 2), (0, 0), (14, 2), (44, 2), (0, 0), (0, 3), (23,
    3), (0, 0), (0, 3), (23, 3), (0, 0), (5, 3), (824, 3), (0, 0), (8, 3), (827, 3), (0, 0), (5,
    3), (824, 3)] : List (Fin 860 × ℚ)) ++ ([(0, 0), (8, 3), (827, 3), (0, 0), (1, -3), (24,
    -3), (0, 0), (1, -3), (24, -3), (0, 0), (815, -3), (34, -3), (0, 0), (817, -3), (39, -3),
    (0, 0), (815, -3), (34, -3), (0, 0), (817, -3), (39, -3), (294, (1 / 5)), (319, (1 / 5)),
    (294, (1 / 5)), (294, (1 / 5)), (319, (1 / 5)), (294, (1 / 5)), (294, (1 / 5)), (319, (1 /
    5)), (294, (1 / 5)), (294, (1 / 5)), (319, (1 / 5)), (294, (1 / 5)), (294, (1 / 5)), (319,
    (1 / 5)), (294, (1 / 5)), (294, (1 / 5)), (319, (1 / 5)), (294, (1 / 5)), (332, (-6 / 5)),
    (315, (-6 / 5)), (289, (-6 / 5)), (353, (-6 / 5)), (311, (-6 / 5)), (286, (-6 / 5)), (332,
    (-6 / 5)), (315, (-6 / 5)), (289, (-6 / 5)), (353, (-6 / 5)), (311, (-6 / 5)), (286, (-6 /
    5))] : List (Fin 860 × ℚ)) ++ ([(370, (-6 / 5)), (304, (-6 / 5)), (280, (-6 / 5)), (370, (-6
    / 5)), (304, (-6 / 5)), (280, (-6 / 5)), (363, (12 / 5)), (308, (12 / 5)), (282, (12 / 5)),
    (363, (12 / 5)), (308, (12 / 5)), (282, (12 / 5)), (373, (12 / 5)), (300, (12 / 5)), (841,
    (12 / 5)), (376, (12 / 5)), (296, (12 / 5)), (839, (12 / 5)), (373, (12 / 5)), (300, (12 /
    5)), (841, (12 / 5)), (376, (12 / 5)), (296, (12 / 5)), (839, (12 / 5)), (324, (-18 / 5)),
    (337, (-18 / 5)), (852, (-18 / 5)), (345, (-18 / 5)), (358, (-18 / 5)), (850, (-18 / 5)),
    (327, (-18 / 5)), (341, (-18 / 5)), (348, (-18 / 5)), (348, (-18 / 5)), (341, (-18 / 5)),
    (327, (-18 / 5)), (850, (-18 / 5)), (358, (-18 / 5)), (345, (-18 / 5)), (852, (-18 / 5)),
    (337, (-18 / 5)), (324, (-18 / 5)), (180, (-6 / 5)), (173, (-6 / 5)), (272, (-6 / 5)), (180,
    (-6 / 5)), (173, (-6 / 5)), (272, (-6 / 5)), (180, (-6 / 5)), (173, (-6 / 5)), (272, (-6 /
    5))] : List (Fin 860 × ℚ)) ++ ([(180, (-6 / 5)), (173, (-6 / 5)), (272, (-6 / 5)), (180, (-6
    / 5)), (173, (-6 / 5)), (272, (-6 / 5)), (180, (-6 / 5)), (173, (-6 / 5)), (272, (-6 / 5)),
    (127, (9 / 5)), (132, (9 / 5)), (226, (9 / 5)), (127, (9 / 5)), (132, (9 / 5)), (226, (9 /
    5)), (144, (9 / 5)), (149, (9 / 5)), (254, (9 / 5)), (159, (9 / 5)), (164, (9 / 5)), (266,
    (9 / 5)), (144, (9 / 5)), (149, (9 / 5)), (254, (9 / 5)), (159, (9 / 5)), (164, (9 / 5)),
    (266, (9 / 5)), (138, (-6 / 5)), (121, (-6 / 5)), (220, (-6 / 5)), (138, (-6 / 5)), (121,
    (-6 / 5)), (220, (-6 / 5)), (153, (-6 / 5)), (140, (-6 / 5)), (248, (-6 / 5)), (168, (-6 /
    5)), (155, (-6 / 5)), (260, (-6 / 5)), (153, (-6 / 5)), (140, (-6 / 5)), (248, (-6 / 5)),
    (168, (-6 / 5)), (155, (-6 / 5)), (260, (-6 / 5)), (658, (1 / 120)), (629, (1 / 120)), (658,
    (1 / 120)), (629, (1 / 120)), (658, (1 / 120)), (629, (1 / 120))] : List (Fin 860 × ℚ)) ++
    ([(658, (1 / 120)), (629, (1 / 120)), (658, (1 / 120)), (629, (1 / 120)), (658, (1 / 120)),
    (629, (1 / 120)), (654, (-3 / 40)), (624, (-3 / 40)), (650, (-3 / 40)), (620, (-3 / 40)),
    (654, (-3 / 40)), (624, (-3 / 40)), (650, (-3 / 40)), (620, (-3 / 40)), (642, (-3 / 40)),
    (612, (-3 / 40)), (642, (-3 / 40)), (612, (-3 / 40)), (646, (3 / 40)), (615, (3 / 40)),
    (646, (3 / 40)), (615, (3 / 40)), (638, (3 / 40)), (607, (3 / 40)), (634, (3 / 40)), (603,
    (3 / 40)), (638, (3 / 40)), (607, (3 / 40)), (634, (3 / 40)), (603, (3 / 40)), (630, (-1 /
    120)), (598, (-1 / 120)), (630, (-1 / 120)), (598, (-1 / 120)), (630, (-1 / 120)), (598, (-1
    / 120)), (630, (-1 / 120)), (598, (-1 / 120)), (630, (-1 / 120)), (598, (-1 / 120)), (630,
    (-1 / 120)), (598, (-1 / 120)), (594, (1 / 10)), (568, (1 / 10)), (594, (1 / 10)), (568, (1
    / 10)), (594, (1 / 10)), (568, (1 / 10)), (594, (1 / 10)), (568, (1 / 10)), (594, (1 / 10))]
    : List (Fin 860 × ℚ)) ++ ([(568, (1 / 10)), (594, (1 / 10)), (568, (1 / 10)), (590, (-3 /
    10)), (563, (-3 / 10)), (586, (-3 / 10)), (559, (-3 / 10)), (590, (-3 / 10)), (563, (-3 /
    10)), (586, (-3 / 10)), (559, (-3 / 10)), (578, (-3 / 10)), (552, (-3 / 10)), (578, (-3 /
    10)), (552, (-3 / 10)), (582, (1 / 10)), (554, (1 / 10)), (582, (1 / 10)), (554, (1 / 10)),
    (574, (1 / 10)), (856, (1 / 10)), (570, (1 / 10)), (854, (1 / 10)), (574, (1 / 10)), (856,
    (1 / 10)), (570, (1 / 10)), (854, (1 / 10)), (513, (-1 / 20)), (544, (-1 / 20)), (513, (-1 /
    20)), (544, (-1 / 20)), (513, (-1 / 20)), (544, (-1 / 20)), (513, (-1 / 20)), (544, (-1 /
    20)), (513, (-1 / 20)), (544, (-1 / 20)), (513, (-1 / 20)), (544, (-1 / 20)), (500, (-1 /
    20)), (524, (-1 / 20)), (500, (-1 / 20)), (524, (-1 / 20)), (504, (-1 / 20)), (533, (-1 /
    20)), (507, (-1 / 20)), (539, (-1 / 20)), (504, (-1 / 20)), (533, (-1 / 20)), (507, (-1 /
    20)), (539, (-1 / 20))] : List (Fin 860 × ℚ))

/-- The records equal the actual dimension-pruned signed pullback computation. -/
theorem records0_checked : CotangentCombination.dimensionRecords
    L24InitialHints.columnIndex (Pi.single 0 1) L24Initial.pullback =
    (records0 : Multiset (Fin 860 × ℚ)) := by
  decide +kernel

/-- Proposed consolidated coefficients, before the weighted marking average. -/
def raw0 : Coordinates 860 :=
  fun i ↦ (if i.val < 430 then (if i.val < 215 then (if i.val < 107 then (if i.val < 53 then (if
    i.val < 26 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then
    6 else (if i.val < 2 then -6 else 0)) else (if i.val < 4 then 0 else (if i.val < 5 then 0
    else 6))) else (if i.val < 9 then (if i.val < 7 then 0 else (if i.val < 8 then 0 else 6))
    else 0)) else (if i.val < 19 then (if i.val < 16 then (if i.val < 14 then 0 else (if i.val <
    15 then 12 else 0)) else 0) else (if i.val < 22 then 0 else (if i.val < 24 then (if i.val <
    23 then 0 else 6) else (if i.val < 25 then -6 else 0))))) else (if i.val < 39 then (if i.val
    < 32 then 0 else (if i.val < 35 then (if i.val < 33 then 0 else (if i.val < 34 then 0 else
    -6)) else 0)) else (if i.val < 46 then (if i.val < 42 then (if i.val < 40 then -6 else 0)
    else (if i.val < 44 then 0 else (if i.val < 45 then 12 else 0))) else (if i.val < 49 then
    (if i.val < 47 then 0 else (if i.val < 48 then 0 else -4)) else 0)))) else (if i.val < 80
    then (if i.val < 66 then (if i.val < 59 then (if i.val < 56 then (if i.val < 54 then 0 else
    (if i.val < 55 then -4 else 0)) else (if i.val < 57 then 0 else (if i.val < 58 then -4 else
    0))) else (if i.val < 62 then 0 else (if i.val < 64 then 0 else (if i.val < 65 then -4 else
    0)))) else 0) else (if i.val < 93 then (if i.val < 86 then 0 else (if i.val < 89 then 0 else
    (if i.val < 91 then (if i.val < 90 then -4 else 0) else 0))) else (if i.val < 100 then (if
    i.val < 96 then 0 else (if i.val < 98 then 0 else (if i.val < 99 then -4 else 0))) else (if
    i.val < 103 then (if i.val < 101 then 0 else (if i.val < 102 then 0 else -4)) else 0)))))
    else (if i.val < 161 then (if i.val < 134 then (if i.val < 120 then 0 else (if i.val < 127
    then (if i.val < 123 then (if i.val < 121 then 0 else (if i.val < 122 then (-12 / 5) else
    0)) else 0) else (if i.val < 130 then (if i.val < 128 then (18 / 5) else 0) else (if i.val <
    132 then 0 else (if i.val < 133 then (18 / 5) else 0))))) else (if i.val < 147 then (if
    i.val < 140 then (if i.val < 137 then 0 else (if i.val < 138 then 0 else (if i.val < 139
    then (-12 / 5) else 0))) else (if i.val < 143 then (if i.val < 141 then (-12 / 5) else 0)
    else (if i.val < 145 then (if i.val < 144 then 0 else (18 / 5)) else 0))) else (if i.val <
    154 then (if i.val < 150 then (if i.val < 148 then 0 else (if i.val < 149 then 0 else (18 /
    5))) else (if i.val < 152 then 0 else (if i.val < 153 then 0 else (-12 / 5)))) else (if
    i.val < 157 then (if i.val < 155 then 0 else (if i.val < 156 then (-12 / 5) else 0)) else
    (if i.val < 159 then 0 else (if i.val < 160 then (18 / 5) else 0)))))) else (if i.val < 188
    then (if i.val < 174 then (if i.val < 167 then (if i.val < 164 then 0 else (if i.val < 165
    then (18 / 5) else 0)) else (if i.val < 170 then (if i.val < 168 then 0 else (if i.val < 169
    then (-12 / 5) else 0)) else (if i.val < 172 then 0 else (if i.val < 173 then 0 else (-36 /
    5))))) else (if i.val < 181 then (if i.val < 177 then 0 else (if i.val < 179 then 0 else (if
    i.val < 180 then 0 else (-36 / 5)))) else 0)) else 0))) else (if i.val < 322 then (if i.val
    < 268 then (if i.val < 241 then (if i.val < 228 then (if i.val < 221 then (if i.val < 218
    then 0 else (if i.val < 219 then 0 else (if i.val < 220 then 0 else (-12 / 5)))) else (if
    i.val < 224 then 0 else (if i.val < 226 then 0 else (if i.val < 227 then (18 / 5) else 0))))
    else 0) else (if i.val < 254 then (if i.val < 247 then 0 else (if i.val < 250 then (if i.val
    < 248 then 0 else (if i.val < 249 then (-12 / 5) else 0)) else 0)) else (if i.val < 261 then
    (if i.val < 257 then (if i.val < 255 then (18 / 5) else 0) else (if i.val < 259 then 0 else
    (if i.val < 260 then 0 else (-12 / 5)))) else (if i.val < 264 then 0 else (if i.val < 266
    then 0 else (if i.val < 267 then (18 / 5) else 0)))))) else (if i.val < 295 then (if i.val <
    281 then (if i.val < 274 then (if i.val < 271 then 0 else (if i.val < 272 then 0 else (if
    i.val < 273 then (-36 / 5) else 0))) else (if i.val < 277 then 0 else (if i.val < 279 then 0
    else (if i.val < 280 then 0 else (-12 / 5))))) else (if i.val < 288 then (if i.val < 284
    then (if i.val < 282 then 0 else (if i.val < 283 then (24 / 5) else 0)) else (if i.val < 286
    then 0 else (if i.val < 287 then (-12 / 5) else 0))) else (if i.val < 291 then (if i.val <
    289 then 0 else (if i.val < 290 then (-12 / 5) else 0)) else (if i.val < 293 then 0 else (if
    i.val < 294 then 0 else (12 / 5)))))) else (if i.val < 308 then (if i.val < 301 then (if
    i.val < 298 then (if i.val < 296 then 0 else (if i.val < 297 then (24 / 5) else 0)) else (if
    i.val < 299 then 0 else (if i.val < 300 then 0 else (24 / 5)))) else (if i.val < 304 then 0
    else (if i.val < 306 then (if i.val < 305 then (-12 / 5) else 0) else 0))) else (if i.val <
    315 then (if i.val < 311 then (if i.val < 309 then (24 / 5) else 0) else (if i.val < 313
    then (if i.val < 312 then (-12 / 5) else 0) else 0)) else (if i.val < 318 then (if i.val <
    316 then (-12 / 5) else 0) else (if i.val < 320 then (if i.val < 319 then 0 else (6 / 5))
    else 0)))))) else (if i.val < 376 then (if i.val < 349 then (if i.val < 335 then (if i.val <
    328 then (if i.val < 325 then (if i.val < 323 then 0 else (if i.val < 324 then 0 else (-36 /
    5))) else (if i.val < 326 then 0 else (if i.val < 327 then 0 else (-36 / 5)))) else (if
    i.val < 331 then 0 else (if i.val < 333 then (if i.val < 332 then 0 else (-12 / 5)) else
    0))) else (if i.val < 342 then (if i.val < 338 then (if i.val < 336 then 0 else (if i.val <
    337 then 0 else (-36 / 5))) else (if i.val < 340 then 0 else (if i.val < 341 then 0 else
    (-36 / 5)))) else (if i.val < 345 then 0 else (if i.val < 347 then (if i.val < 346 then (-36
    / 5) else 0) else (if i.val < 348 then 0 else (-36 / 5)))))) else (if i.val < 362 then (if
    i.val < 355 then (if i.val < 352 then 0 else (if i.val < 353 then 0 else (if i.val < 354
    then (-12 / 5) else 0))) else (if i.val < 358 then 0 else (if i.val < 360 then (if i.val <
    359 then (-36 / 5) else 0) else 0))) else (if i.val < 369 then (if i.val < 365 then (if
    i.val < 363 then 0 else (if i.val < 364 then (24 / 5) else 0)) else 0) else (if i.val < 372
    then (if i.val < 370 then 0 else (if i.val < 371 then (-12 / 5) else 0)) else (if i.val <
    374 then (if i.val < 373 then 0 else (24 / 5)) else 0))))) else (if i.val < 403 then (if
    i.val < 389 then (if i.val < 382 then (if i.val < 379 then (if i.val < 377 then (24 / 5)
    else 0) else 0) else 0) else 0) else 0)))) else (if i.val < 645 then (if i.val < 537 then
    (if i.val < 483 then 0 else (if i.val < 510 then (if i.val < 496 then 0 else (if i.val < 503
    then (if i.val < 499 then 0 else (if i.val < 501 then (if i.val < 500 then 0 else (-1 / 10))
    else 0)) else (if i.val < 506 then (if i.val < 504 then 0 else (if i.val < 505 then (-1 /
    10) else 0)) else (if i.val < 508 then (if i.val < 507 then 0 else (-1 / 10)) else 0))))
    else (if i.val < 523 then (if i.val < 516 then (if i.val < 513 then 0 else (if i.val < 514
    then (-3 / 10) else 0)) else 0) else (if i.val < 530 then (if i.val < 526 then (if i.val <
    524 then 0 else (if i.val < 525 then (-1 / 10) else 0)) else 0) else (if i.val < 533 then 0
    else (if i.val < 535 then (if i.val < 534 then (-1 / 10) else 0) else 0)))))) else (if i.val
    < 591 then (if i.val < 564 then (if i.val < 550 then (if i.val < 543 then (if i.val < 540
    then (if i.val < 538 then 0 else (if i.val < 539 then 0 else (-1 / 10))) else 0) else (if
    i.val < 546 then (if i.val < 544 then 0 else (if i.val < 545 then (-3 / 10) else 0)) else
    0)) else (if i.val < 557 then (if i.val < 553 then (if i.val < 551 then 0 else (if i.val <
    552 then 0 else (-3 / 5))) else (if i.val < 555 then (if i.val < 554 then 0 else (1 / 5))
    else 0)) else (if i.val < 560 then (if i.val < 558 then 0 else (if i.val < 559 then 0 else
    (-3 / 5))) else (if i.val < 562 then 0 else (if i.val < 563 then 0 else (-3 / 5)))))) else
    (if i.val < 577 then (if i.val < 570 then (if i.val < 567 then 0 else (if i.val < 568 then 0
    else (if i.val < 569 then (3 / 5) else 0))) else (if i.val < 573 then (if i.val < 571 then
    (1 / 5) else 0) else (if i.val < 575 then (if i.val < 574 then 0 else (1 / 5)) else 0)))
    else (if i.val < 584 then (if i.val < 580 then (if i.val < 578 then 0 else (if i.val < 579
    then (-3 / 5) else 0)) else (if i.val < 582 then 0 else (if i.val < 583 then (1 / 5) else
    0))) else (if i.val < 587 then (if i.val < 585 then 0 else (if i.val < 586 then 0 else (-3 /
    5))) else (if i.val < 589 then 0 else (if i.val < 590 then 0 else (-3 / 5))))))) else (if
    i.val < 618 then (if i.val < 604 then (if i.val < 597 then (if i.val < 594 then 0 else (if
    i.val < 595 then (3 / 5) else 0)) else (if i.val < 600 then (if i.val < 598 then 0 else (if
    i.val < 599 then (-1 / 20) else 0)) else (if i.val < 602 then 0 else (if i.val < 603 then 0
    else (3 / 20))))) else (if i.val < 611 then (if i.val < 607 then 0 else (if i.val < 609 then
    (if i.val < 608 then (3 / 20) else 0) else 0)) else (if i.val < 614 then (if i.val < 612
    then 0 else (if i.val < 613 then (-3 / 20) else 0)) else (if i.val < 616 then (if i.val <
    615 then 0 else (3 / 20)) else 0)))) else (if i.val < 631 then (if i.val < 624 then (if
    i.val < 621 then (if i.val < 619 then 0 else (if i.val < 620 then 0 else (-3 / 20))) else 0)
    else (if i.val < 627 then (if i.val < 625 then (-3 / 20) else 0) else (if i.val < 629 then 0
    else (if i.val < 630 then (1 / 20) else (-1 / 20))))) else (if i.val < 638 then (if i.val <
    634 then 0 else (if i.val < 636 then (if i.val < 635 then (3 / 20) else 0) else 0)) else (if
    i.val < 641 then (if i.val < 639 then (3 / 20) else 0) else (if i.val < 643 then (if i.val <
    642 then 0 else (-3 / 20)) else 0))))))) else (if i.val < 752 then (if i.val < 698 then (if
    i.val < 671 then (if i.val < 658 then (if i.val < 651 then (if i.val < 648 then (if i.val <
    646 then 0 else (if i.val < 647 then (3 / 20) else 0)) else (if i.val < 649 then 0 else (if
    i.val < 650 then 0 else (-3 / 20)))) else (if i.val < 654 then 0 else (if i.val < 656 then
    (if i.val < 655 then (-3 / 20) else 0) else 0))) else (if i.val < 664 then (if i.val < 661
    then (if i.val < 659 then (1 / 20) else 0) else 0) else 0)) else 0) else 0) else (if i.val <
    806 then 0 else (if i.val < 833 then (if i.val < 819 then (if i.val < 812 then 0 else (if
    i.val < 815 then 0 else (if i.val < 817 then (if i.val < 816 then -6 else 0) else (if i.val
    < 818 then -6 else 0)))) else (if i.val < 826 then (if i.val < 822 then 0 else (if i.val <
    824 then 0 else (if i.val < 825 then 6 else 0))) else (if i.val < 829 then (if i.val < 827
    then 0 else (if i.val < 828 then 6 else 0)) else (if i.val < 831 then (if i.val < 830 then 0
    else -4) else (if i.val < 832 then 0 else -4))))) else (if i.val < 846 then (if i.val < 839
    then 0 else (if i.val < 842 then (if i.val < 840 then (24 / 5) else (if i.val < 841 then 0
    else (24 / 5))) else 0)) else (if i.val < 853 then (if i.val < 849 then 0 else (if i.val <
    851 then (if i.val < 850 then 0 else (-36 / 5)) else (if i.val < 852 then 0 else (-36 /
    5)))) else (if i.val < 856 then (if i.val < 854 then 0 else (if i.val < 855 then (1 / 5)
    else 0)) else (if i.val < 858 then (if i.val < 857 then (1 / 5) else 0) else 0)))))))))

/-- Kernel arithmetic adds every signed coefficient at its proposed destination. -/
theorem raw0_checked : StrataOperation.recordCoordinates records0 = raw0 := by
  decide +kernel

/-- Consolidation of the actual signed pullback contribution. -/
theorem coordinates0_checked :
    CotangentCombination.recordCoordinates (CotangentCombination.dimensionRecords
      L24InitialHints.columnIndex (Pi.single 0 1) L24Initial.pullback) = raw0 := by
  rw [records0_checked]
  simpa only [CotangentCombination.recordCoordinates, Multiset.map_coe, Multiset.sum_coe,
    StrataOperation.recordCoordinates_eq_sum] using raw0_checked

set_option maxHeartbeats 800000 in
-- Elaborating the 306 exact records exceeds the default declaration budget.
/-- Proposed records for the psi-1 term; no multiplicity is removed. -/
def records1 : List (Fin 860 × ℚ) :=
  ([(0, 0), (55, -2), (0, 0), (0, 0), (55, -2), (0, 0), (0, 0), (0, 0), (99, -2), (0, 0), (0,
    0), (103, -2), (0, 0), (0, 0), (99, -2), (0, 0), (0, 0), (103, -2), (71, -2), (819, 2), (45,
    2), (71, -2), (819, 2), (45, 2), (71, -2), (819, 2), (45, 2), (71, -2), (819, 2), (45, 2),
    (71, -2), (819, 2), (45, 2), (71, -2), (819, 2), (45, 2), (0, 0), (2, 3), (29, 3), (0, 0),
    (2, 3), (29, 3), (0, 0), (0, 0), (35, 3), (0, 0), (0, 0), (40, 3), (0, 0), (0, 0), (35, 3)]
    : List (Fin 860 × ℚ)) ++ ([(0, 0), (0, 0), (40, 3), (50, 3), (3, -3), (30, -3), (50, 3), (3,
    -3), (30, -3), (0, 0), (0, 0), (825, -3), (0, 0), (0, 0), (828, -3), (0, 0), (0, 0), (825,
    -3), (0, 0), (0, 0), (828, -3), (291, (1 / 5)), (320, (1 / 5)), (291, (1 / 5)), (291, (1 /
    5)), (320, (1 / 5)), (291, (1 / 5)), (291, (1 / 5)), (320, (1 / 5)), (291, (1 / 5)), (291,
    (1 / 5)), (320, (1 / 5)), (291, (1 / 5)), (291, (1 / 5)), (320, (1 / 5)), (291, (1 / 5)),
    (291, (1 / 5)), (320, (1 / 5)), (291, (1 / 5)), (330, (-6 / 5)), (316, (-6 / 5)), (844, (-6
    / 5)), (351, (-6 / 5)), (312, (-6 / 5)), (843, (-6 / 5)), (330, (-6 / 5)), (316, (-6 / 5)),
    (844, (-6 / 5)), (351, (-6 / 5)), (312, (-6 / 5)), (843, (-6 / 5))] : List (Fin 860 × ℚ)) ++
    ([(367, (-6 / 5)), (307, (-6 / 5)), (281, (-6 / 5)), (367, (-6 / 5)), (307, (-6 / 5)), (281,
    (-6 / 5)), (0, 0), (847, (12 / 5)), (0, 0), (0, 0), (847, (12 / 5)), (0, 0), (371, (12 /
    5)), (302, (12 / 5)), (277, (12 / 5)), (374, (12 / 5)), (298, (12 / 5)), (276, (12 / 5)),
    (371, (12 / 5)), (302, (12 / 5)), (277, (12 / 5)), (374, (12 / 5)), (298, (12 / 5)), (276,
    (12 / 5)), (325, (-18 / 5)), (339, (-18 / 5)), (366, (-18 / 5)), (346, (-18 / 5)), (360,
    (-18 / 5)), (365, (-18 / 5)), (0, 0), (342, (-18 / 5)), (0, 0), (0, 0), (342, (-18 / 5)),
    (0, 0), (365, (-18 / 5)), (360, (-18 / 5)), (346, (-18 / 5)), (366, (-18 / 5)), (339, (-18 /
    5)), (325, (-18 / 5)), (836, (-6 / 5)), (170, (-6 / 5)), (273, (-6 / 5)), (836, (-6 / 5)),
    (170, (-6 / 5)), (273, (-6 / 5)), (836, (-6 / 5)), (170, (-6 / 5)), (273, (-6 / 5))] : List
    (Fin 860 × ℚ)) ++ ([(836, (-6 / 5)), (170, (-6 / 5)), (273, (-6 / 5)), (836, (-6 / 5)),
    (170, (-6 / 5)), (273, (-6 / 5)), (836, (-6 / 5)), (170, (-6 / 5)), (273, (-6 / 5)), (128,
    (9 / 5)), (130, (9 / 5)), (231, (9 / 5)), (128, (9 / 5)), (130, (9 / 5)), (231, (9 / 5)),
    (0, 0), (0, 0), (837, (9 / 5)), (0, 0), (0, 0), (838, (9 / 5)), (0, 0), (0, 0), (837, (9 /
    5)), (0, 0), (0, 0), (838, (9 / 5)), (135, (-6 / 5)), (122, (-6 / 5)), (223, (-6 / 5)),
    (135, (-6 / 5)), (122, (-6 / 5)), (223, (-6 / 5)), (0, 0), (0, 0), (249, (-6 / 5)), (0, 0),
    (0, 0), (261, (-6 / 5)), (0, 0), (0, 0), (249, (-6 / 5)), (0, 0), (0, 0), (261, (-6 / 5)),
    (659, (1 / 120)), (626, (1 / 120)), (659, (1 / 120)), (626, (1 / 120)), (659, (1 / 120)),
    (626, (1 / 120))] : List (Fin 860 × ℚ)) ++ ([(659, (1 / 120)), (626, (1 / 120)), (659, (1 /
    120)), (626, (1 / 120)), (659, (1 / 120)), (626, (1 / 120)), (655, (-3 / 40)), (622, (-3 /
    40)), (651, (-3 / 40)), (618, (-3 / 40)), (655, (-3 / 40)), (622, (-3 / 40)), (651, (-3 /
    40)), (618, (-3 / 40)), (645, (-3 / 40)), (613, (-3 / 40)), (645, (-3 / 40)), (613, (-3 /
    40)), (647, (3 / 40)), (614, (3 / 40)), (647, (3 / 40)), (614, (3 / 40)), (640, (3 / 40)),
    (608, (3 / 40)), (636, (3 / 40)), (604, (3 / 40)), (640, (3 / 40)), (608, (3 / 40)), (636,
    (3 / 40)), (604, (3 / 40)), (631, (-1 / 120)), (599, (-1 / 120)), (631, (-1 / 120)), (599,
    (-1 / 120)), (631, (-1 / 120)), (599, (-1 / 120)), (631, (-1 / 120)), (599, (-1 / 120)),
    (631, (-1 / 120)), (599, (-1 / 120)), (631, (-1 / 120)), (599, (-1 / 120)), (595, (1 / 10)),
    (565, (1 / 10)), (595, (1 / 10)), (565, (1 / 10)), (595, (1 / 10)), (565, (1 / 10)), (595,
    (1 / 10)), (565, (1 / 10)), (595, (1 / 10))] : List (Fin 860 × ℚ)) ++ ([(565, (1 / 10)),
    (595, (1 / 10)), (565, (1 / 10)), (591, (-3 / 10)), (561, (-3 / 10)), (587, (-3 / 10)),
    (557, (-3 / 10)), (591, (-3 / 10)), (561, (-3 / 10)), (587, (-3 / 10)), (557, (-3 / 10)),
    (581, (-3 / 10)), (553, (-3 / 10)), (581, (-3 / 10)), (553, (-3 / 10)), (583, (1 / 10)), (0,
    0), (583, (1 / 10)), (0, 0), (576, (1 / 10)), (549, (1 / 10)), (572, (1 / 10)), (548, (1 /
    10)), (576, (1 / 10)), (549, (1 / 10)), (572, (1 / 10)), (548, (1 / 10)), (510, (-1 / 20)),
    (545, (-1 / 20)), (510, (-1 / 20)), (545, (-1 / 20)), (510, (-1 / 20)), (545, (-1 / 20)),
    (510, (-1 / 20)), (545, (-1 / 20)), (510, (-1 / 20)), (545, (-1 / 20)), (510, (-1 / 20)),
    (545, (-1 / 20)), (501, (-1 / 20)), (527, (-1 / 20)), (501, (-1 / 20)), (527, (-1 / 20)),
    (0, 0), (534, (-1 / 20)), (0, 0), (540, (-1 / 20)), (0, 0), (534, (-1 / 20)), (0, 0), (540,
    (-1 / 20))] : List (Fin 860 × ℚ))

/-- The records equal the actual dimension-pruned signed pullback computation. -/
theorem records1_checked : CotangentCombination.dimensionRecords
    L24InitialHints.columnIndex (Pi.single 1 1) L24Initial.pullback =
    (records1 : Multiset (Fin 860 × ℚ)) := by
  decide +kernel

/-- Proposed consolidated coefficients, before the weighted marking average. -/
def raw1 : Coordinates 860 :=
  fun i ↦ (if i.val < 430 then (if i.val < 215 then (if i.val < 107 then (if i.val < 53 then (if
    i.val < 26 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then
    0 else (if i.val < 2 then 0 else 6)) else (if i.val < 4 then -6 else 0)) else 0) else 0)
    else (if i.val < 39 then (if i.val < 32 then (if i.val < 29 then 0 else (if i.val < 30 then
    6 else (if i.val < 31 then -6 else 0))) else (if i.val < 35 then 0 else (if i.val < 37 then
    (if i.val < 36 then 6 else 0) else 0))) else (if i.val < 46 then (if i.val < 42 then (if
    i.val < 40 then 0 else (if i.val < 41 then 6 else 0)) else (if i.val < 44 then 0 else (if
    i.val < 45 then 0 else 12))) else (if i.val < 49 then 0 else (if i.val < 51 then (if i.val <
    50 then 0 else 6) else 0))))) else (if i.val < 80 then (if i.val < 66 then (if i.val < 59
    then (if i.val < 56 then (if i.val < 54 then 0 else (if i.val < 55 then 0 else -4)) else 0)
    else 0) else (if i.val < 73 then (if i.val < 69 then 0 else (if i.val < 71 then 0 else (if
    i.val < 72 then -12 else 0))) else 0)) else (if i.val < 93 then 0 else (if i.val < 100 then
    (if i.val < 96 then 0 else (if i.val < 98 then 0 else (if i.val < 99 then 0 else -4))) else
    (if i.val < 103 then 0 else (if i.val < 105 then (if i.val < 104 then -4 else 0) else
    0)))))) else (if i.val < 161 then (if i.val < 134 then (if i.val < 120 then 0 else (if i.val
    < 127 then (if i.val < 123 then (if i.val < 121 then 0 else (if i.val < 122 then 0 else (-12
    / 5))) else 0) else (if i.val < 130 then (if i.val < 128 then 0 else (if i.val < 129 then
    (18 / 5) else 0)) else (if i.val < 132 then (if i.val < 131 then (18 / 5) else 0) else 0))))
    else (if i.val < 147 then (if i.val < 140 then (if i.val < 137 then (if i.val < 135 then 0
    else (if i.val < 136 then (-12 / 5) else 0)) else 0) else 0) else 0)) else (if i.val < 188
    then (if i.val < 174 then (if i.val < 167 then 0 else (if i.val < 170 then 0 else (if i.val
    < 172 then (if i.val < 171 then (-36 / 5) else 0) else 0))) else 0) else 0))) else (if i.val
    < 322 then (if i.val < 268 then (if i.val < 241 then (if i.val < 228 then (if i.val < 221
    then 0 else (if i.val < 224 then (if i.val < 222 then 0 else (if i.val < 223 then 0 else
    (-12 / 5))) else 0)) else (if i.val < 234 then (if i.val < 231 then 0 else (if i.val < 232
    then (18 / 5) else 0)) else 0)) else (if i.val < 254 then (if i.val < 247 then 0 else (if
    i.val < 250 then (if i.val < 248 then 0 else (if i.val < 249 then 0 else (-12 / 5))) else
    0)) else (if i.val < 261 then 0 else (if i.val < 264 then (if i.val < 262 then (-12 / 5)
    else 0) else 0)))) else (if i.val < 295 then (if i.val < 281 then (if i.val < 274 then (if
    i.val < 271 then 0 else (if i.val < 272 then 0 else (if i.val < 273 then 0 else (-36 / 5))))
    else (if i.val < 277 then (if i.val < 275 then 0 else (if i.val < 276 then 0 else (24 / 5)))
    else (if i.val < 279 then (if i.val < 278 then (24 / 5) else 0) else 0))) else (if i.val <
    288 then (if i.val < 284 then (if i.val < 282 then (-12 / 5) else 0) else 0) else (if i.val
    < 291 then 0 else (if i.val < 293 then (if i.val < 292 then (12 / 5) else 0) else 0)))) else
    (if i.val < 308 then (if i.val < 301 then (if i.val < 298 then 0 else (if i.val < 299 then
    (24 / 5) else 0)) else (if i.val < 304 then (if i.val < 302 then 0 else (if i.val < 303 then
    (24 / 5) else 0)) else (if i.val < 306 then 0 else (if i.val < 307 then 0 else (-12 / 5)))))
    else (if i.val < 315 then (if i.val < 311 then 0 else (if i.val < 313 then (if i.val < 312
    then 0 else (-12 / 5)) else 0)) else (if i.val < 318 then (if i.val < 316 then 0 else (if
    i.val < 317 then (-12 / 5) else 0)) else (if i.val < 320 then 0 else (if i.val < 321 then (6
    / 5) else 0))))))) else (if i.val < 376 then (if i.val < 349 then (if i.val < 335 then (if
    i.val < 328 then (if i.val < 325 then 0 else (if i.val < 326 then (-36 / 5) else 0)) else
    (if i.val < 331 then (if i.val < 329 then 0 else (if i.val < 330 then 0 else (-12 / 5)))
    else 0)) else (if i.val < 342 then (if i.val < 338 then 0 else (if i.val < 340 then (if
    i.val < 339 then 0 else (-36 / 5)) else 0)) else (if i.val < 345 then (if i.val < 343 then
    (-36 / 5) else 0) else (if i.val < 347 then (if i.val < 346 then 0 else (-36 / 5)) else
    0)))) else (if i.val < 362 then (if i.val < 355 then (if i.val < 352 then (if i.val < 350
    then 0 else (if i.val < 351 then 0 else (-12 / 5))) else 0) else (if i.val < 358 then 0 else
    (if i.val < 360 then 0 else (if i.val < 361 then (-36 / 5) else 0)))) else (if i.val < 369
    then (if i.val < 365 then 0 else (if i.val < 367 then (-36 / 5) else (if i.val < 368 then
    (-12 / 5) else 0))) else (if i.val < 372 then (if i.val < 370 then 0 else (if i.val < 371
    then 0 else (24 / 5))) else (if i.val < 374 then 0 else (if i.val < 375 then (24 / 5) else
    0)))))) else 0))) else (if i.val < 645 then (if i.val < 537 then (if i.val < 483 then 0 else
    (if i.val < 510 then (if i.val < 496 then 0 else (if i.val < 503 then (if i.val < 499 then 0
    else (if i.val < 501 then 0 else (if i.val < 502 then (-1 / 10) else 0))) else 0)) else (if
    i.val < 523 then (if i.val < 516 then (if i.val < 513 then (if i.val < 511 then (-3 / 10)
    else 0) else 0) else 0) else (if i.val < 530 then (if i.val < 526 then 0 else (if i.val <
    528 then (if i.val < 527 then 0 else (-1 / 10)) else 0)) else (if i.val < 533 then 0 else
    (if i.val < 535 then (if i.val < 534 then 0 else (-1 / 10)) else 0)))))) else (if i.val <
    591 then (if i.val < 564 then (if i.val < 550 then (if i.val < 543 then (if i.val < 540 then
    0 else (if i.val < 541 then (-1 / 10) else 0)) else (if i.val < 546 then (if i.val < 544
    then 0 else (if i.val < 545 then 0 else (-3 / 10))) else (if i.val < 548 then 0 else (1 /
    5)))) else (if i.val < 557 then (if i.val < 553 then 0 else (if i.val < 555 then (if i.val <
    554 then (-3 / 5) else 0) else 0)) else (if i.val < 560 then (if i.val < 558 then (-3 / 5)
    else 0) else (if i.val < 562 then (if i.val < 561 then 0 else (-3 / 5)) else 0)))) else (if
    i.val < 577 then (if i.val < 570 then (if i.val < 567 then (if i.val < 565 then 0 else (if
    i.val < 566 then (3 / 5) else 0)) else 0) else (if i.val < 573 then (if i.val < 571 then 0
    else (if i.val < 572 then 0 else (1 / 5))) else (if i.val < 575 then 0 else (if i.val < 576
    then 0 else (1 / 5))))) else (if i.val < 584 then (if i.val < 580 then 0 else (if i.val <
    582 then (if i.val < 581 then 0 else (-3 / 5)) else (if i.val < 583 then 0 else (1 / 5))))
    else (if i.val < 587 then 0 else (if i.val < 589 then (if i.val < 588 then (-3 / 5) else 0)
    else 0))))) else (if i.val < 618 then (if i.val < 604 then (if i.val < 597 then (if i.val <
    594 then (if i.val < 592 then (-3 / 5) else 0) else (if i.val < 595 then 0 else (if i.val <
    596 then (3 / 5) else 0))) else (if i.val < 600 then (if i.val < 598 then 0 else (if i.val <
    599 then 0 else (-1 / 20))) else 0)) else (if i.val < 611 then (if i.val < 607 then (if
    i.val < 605 then (3 / 20) else 0) else (if i.val < 609 then (if i.val < 608 then 0 else (3 /
    20)) else 0)) else (if i.val < 614 then (if i.val < 612 then 0 else (if i.val < 613 then 0
    else (-3 / 20))) else (if i.val < 616 then (if i.val < 615 then (3 / 20) else 0) else 0))))
    else (if i.val < 631 then (if i.val < 624 then (if i.val < 621 then (if i.val < 619 then (-3
    / 20) else 0) else (if i.val < 622 then 0 else (if i.val < 623 then (-3 / 20) else 0))) else
    (if i.val < 627 then (if i.val < 625 then 0 else (if i.val < 626 then 0 else (1 / 20))) else
    0)) else (if i.val < 638 then (if i.val < 634 then (if i.val < 632 then (-1 / 20) else 0)
    else (if i.val < 636 then 0 else (if i.val < 637 then (3 / 20) else 0))) else (if i.val <
    641 then (if i.val < 639 then 0 else (if i.val < 640 then 0 else (3 / 20))) else 0))))))
    else (if i.val < 752 then (if i.val < 698 then (if i.val < 671 then (if i.val < 658 then (if
    i.val < 651 then (if i.val < 648 then (if i.val < 646 then (-3 / 20) else (if i.val < 647
    then 0 else (3 / 20))) else 0) else (if i.val < 654 then (if i.val < 652 then (-3 / 20) else
    0) else (if i.val < 656 then (if i.val < 655 then 0 else (-3 / 20)) else 0))) else (if i.val
    < 664 then (if i.val < 661 then (if i.val < 659 then 0 else (if i.val < 660 then (1 / 20)
    else 0)) else 0) else 0)) else 0) else 0) else (if i.val < 806 then 0 else (if i.val < 833
    then (if i.val < 819 then 0 else (if i.val < 826 then (if i.val < 822 then (if i.val < 820
    then 12 else 0) else (if i.val < 824 then 0 else (if i.val < 825 then 0 else -6))) else (if
    i.val < 829 then (if i.val < 827 then 0 else (if i.val < 828 then 0 else -6)) else 0))) else
    (if i.val < 846 then (if i.val < 839 then (if i.val < 836 then 0 else (if i.val < 837 then
    (-36 / 5) else (18 / 5))) else (if i.val < 842 then 0 else (if i.val < 844 then (if i.val <
    843 then 0 else (-12 / 5)) else (if i.val < 845 then (-12 / 5) else 0)))) else (if i.val <
    853 then (if i.val < 849 then (if i.val < 847 then 0 else (if i.val < 848 then (24 / 5) else
    0)) else 0) else 0)))))))

/-- Kernel arithmetic adds every signed coefficient at its proposed destination. -/
theorem raw1_checked : StrataOperation.recordCoordinates records1 = raw1 := by
  decide +kernel

/-- Consolidation of the actual signed pullback contribution. -/
theorem coordinates1_checked :
    CotangentCombination.recordCoordinates (CotangentCombination.dimensionRecords
      L24InitialHints.columnIndex (Pi.single 1 1) L24Initial.pullback) = raw1 := by
  rw [records1_checked]
  simpa only [CotangentCombination.recordCoordinates, Multiset.map_coe, Multiset.sum_coe,
    StrataOperation.recordCoordinates_eq_sum] using raw1_checked

set_option maxHeartbeats 800000 in
-- Elaborating the 306 exact records exceeds the default declaration budget.
/-- Proposed records for the psi-2 term; no multiplicity is removed. -/
def records2 : List (Fin 860 × ℚ) :=
  ([(0, 0), (0, 0), (90, -2), (0, 0), (0, 0), (90, -2), (0, 0), (831, -2), (0, 0), (0, 0), (0,
    0), (104, -2), (0, 0), (831, -2), (0, 0), (0, 0), (0, 0), (104, -2), (72, -2), (11, 2), (46,
    2), (72, -2), (11, 2), (46, 2), (72, -2), (11, 2), (46, 2), (72, -2), (11, 2), (46, 2), (72,
    -2), (11, 2), (46, 2), (72, -2), (11, 2), (46, 2), (0, 0), (0, 0), (25, 3), (0, 0), (0, 0),
    (25, 3), (0, 0), (6, 3), (37, 3), (0, 0), (0, 0), (829, 3), (0, 0), (6, 3), (37, 3)] : List
    (Fin 860 × ℚ)) ++ ([(0, 0), (0, 0), (829, 3), (0, 0), (0, 0), (26, -3), (0, 0), (0, 0), (26,
    -3), (59, 3), (816, -3), (38, -3), (0, 0), (0, 0), (41, -3), (59, 3), (816, -3), (38, -3),
    (0, 0), (0, 0), (41, -3), (292, (1 / 5)), (321, (1 / 5)), (292, (1 / 5)), (292, (1 / 5)),
    (321, (1 / 5)), (292, (1 / 5)), (292, (1 / 5)), (321, (1 / 5)), (292, (1 / 5)), (292, (1 /
    5)), (321, (1 / 5)), (292, (1 / 5)), (292, (1 / 5)), (321, (1 / 5)), (292, (1 / 5)), (292,
    (1 / 5)), (321, (1 / 5)), (292, (1 / 5)), (331, (-6 / 5)), (317, (-6 / 5)), (288, (-6 / 5)),
    (350, (-6 / 5)), (314, (-6 / 5)), (287, (-6 / 5)), (331, (-6 / 5)), (317, (-6 / 5)), (288,
    (-6 / 5)), (350, (-6 / 5)), (314, (-6 / 5)), (287, (-6 / 5))] : List (Fin 860 × ℚ)) ++
    ([(368, (-6 / 5)), (305, (-6 / 5)), (278, (-6 / 5)), (368, (-6 / 5)), (305, (-6 / 5)), (278,
    (-6 / 5)), (361, (12 / 5)), (309, (12 / 5)), (283, (12 / 5)), (361, (12 / 5)), (309, (12 /
    5)), (283, (12 / 5)), (0, 0), (301, (12 / 5)), (0, 0), (375, (12 / 5)), (299, (12 / 5)),
    (840, (12 / 5)), (0, 0), (301, (12 / 5)), (0, 0), (375, (12 / 5)), (299, (12 / 5)), (840,
    (12 / 5)), (0, 0), (338, (-18 / 5)), (0, 0), (344, (-18 / 5)), (357, (-18 / 5)), (851, (-18
    / 5)), (328, (-18 / 5)), (343, (-18 / 5)), (347, (-18 / 5)), (347, (-18 / 5)), (343, (-18 /
    5)), (328, (-18 / 5)), (851, (-18 / 5)), (357, (-18 / 5)), (344, (-18 / 5)), (0, 0), (338,
    (-18 / 5)), (0, 0), (176, (-6 / 5)), (171, (-6 / 5)), (274, (-6 / 5)), (176, (-6 / 5)),
    (171, (-6 / 5)), (274, (-6 / 5)), (176, (-6 / 5)), (171, (-6 / 5)), (274, (-6 / 5))] : List
    (Fin 860 × ℚ)) ++ ([(176, (-6 / 5)), (171, (-6 / 5)), (274, (-6 / 5)), (176, (-6 / 5)),
    (171, (-6 / 5)), (274, (-6 / 5)), (176, (-6 / 5)), (171, (-6 / 5)), (274, (-6 / 5)), (0, 0),
    (0, 0), (227, (9 / 5)), (0, 0), (0, 0), (227, (9 / 5)), (145, (9 / 5)), (147, (9 / 5)),
    (258, (9 / 5)), (0, 0), (0, 0), (267, (9 / 5)), (145, (9 / 5)), (147, (9 / 5)), (258, (9 /
    5)), (0, 0), (0, 0), (267, (9 / 5)), (0, 0), (0, 0), (221, (-6 / 5)), (0, 0), (0, 0), (221,
    (-6 / 5)), (151, (-6 / 5)), (141, (-6 / 5)), (251, (-6 / 5)), (0, 0), (0, 0), (262, (-6 /
    5)), (151, (-6 / 5)), (141, (-6 / 5)), (251, (-6 / 5)), (0, 0), (0, 0), (262, (-6 / 5)),
    (660, (1 / 120)), (627, (1 / 120)), (660, (1 / 120)), (627, (1 / 120)), (660, (1 / 120)),
    (627, (1 / 120))] : List (Fin 860 × ℚ)) ++ ([(660, (1 / 120)), (627, (1 / 120)), (660, (1 /
    120)), (627, (1 / 120)), (660, (1 / 120)), (627, (1 / 120)), (656, (-3 / 40)), (623, (-3 /
    40)), (653, (-3 / 40)), (621, (-3 / 40)), (656, (-3 / 40)), (623, (-3 / 40)), (653, (-3 /
    40)), (621, (-3 / 40)), (643, (-3 / 40)), (610, (-3 / 40)), (643, (-3 / 40)), (610, (-3 /
    40)), (648, (3 / 40)), (616, (3 / 40)), (648, (3 / 40)), (616, (3 / 40)), (639, (3 / 40)),
    (606, (3 / 40)), (637, (3 / 40)), (605, (3 / 40)), (639, (3 / 40)), (606, (3 / 40)), (637,
    (3 / 40)), (605, (3 / 40)), (632, (-1 / 120)), (600, (-1 / 120)), (632, (-1 / 120)), (600,
    (-1 / 120)), (632, (-1 / 120)), (600, (-1 / 120)), (632, (-1 / 120)), (600, (-1 / 120)),
    (632, (-1 / 120)), (600, (-1 / 120)), (632, (-1 / 120)), (600, (-1 / 120)), (596, (1 / 10)),
    (566, (1 / 10)), (596, (1 / 10)), (566, (1 / 10)), (596, (1 / 10)), (566, (1 / 10)), (596,
    (1 / 10)), (566, (1 / 10)), (596, (1 / 10))] : List (Fin 860 × ℚ)) ++ ([(566, (1 / 10)),
    (596, (1 / 10)), (566, (1 / 10)), (592, (-3 / 10)), (562, (-3 / 10)), (589, (-3 / 10)),
    (560, (-3 / 10)), (592, (-3 / 10)), (562, (-3 / 10)), (589, (-3 / 10)), (560, (-3 / 10)),
    (579, (-3 / 10)), (550, (-3 / 10)), (579, (-3 / 10)), (550, (-3 / 10)), (584, (1 / 10)),
    (555, (1 / 10)), (584, (1 / 10)), (555, (1 / 10)), (575, (1 / 10)), (0, 0), (573, (1 / 10)),
    (855, (1 / 10)), (575, (1 / 10)), (0, 0), (573, (1 / 10)), (855, (1 / 10)), (511, (-1 /
    20)), (546, (-1 / 20)), (511, (-1 / 20)), (546, (-1 / 20)), (511, (-1 / 20)), (546, (-1 /
    20)), (511, (-1 / 20)), (546, (-1 / 20)), (511, (-1 / 20)), (546, (-1 / 20)), (511, (-1 /
    20)), (546, (-1 / 20)), (0, 0), (525, (-1 / 20)), (0, 0), (525, (-1 / 20)), (505, (-1 /
    20)), (536, (-1 / 20)), (0, 0), (541, (-1 / 20)), (505, (-1 / 20)), (536, (-1 / 20)), (0,
    0), (541, (-1 / 20))] : List (Fin 860 × ℚ))

/-- The records equal the actual dimension-pruned signed pullback computation. -/
theorem records2_checked : CotangentCombination.dimensionRecords
    L24InitialHints.columnIndex (Pi.single 2 1) L24Initial.pullback =
    (records2 : Multiset (Fin 860 × ℚ)) := by
  decide +kernel

/-- Proposed consolidated coefficients, before the weighted marking average. -/
def raw2 : Coordinates 860 :=
  fun i ↦ (if i.val < 430 then (if i.val < 215 then (if i.val < 107 then (if i.val < 53 then (if
    i.val < 26 then (if i.val < 13 then (if i.val < 6 then 0 else (if i.val < 9 then (if i.val <
    7 then 6 else 0) else (if i.val < 11 then 0 else (if i.val < 12 then 12 else 0)))) else (if
    i.val < 19 then 0 else (if i.val < 22 then 0 else (if i.val < 24 then 0 else (if i.val < 25
    then 0 else 6))))) else (if i.val < 39 then (if i.val < 32 then (if i.val < 29 then (if
    i.val < 27 then -6 else 0) else 0) else (if i.val < 35 then 0 else (if i.val < 37 then 0
    else (if i.val < 38 then 6 else -6)))) else (if i.val < 46 then (if i.val < 42 then (if
    i.val < 40 then 0 else (if i.val < 41 then 0 else -6)) else 0) else (if i.val < 49 then (if
    i.val < 47 then 12 else 0) else 0)))) else (if i.val < 80 then (if i.val < 66 then (if i.val
    < 59 then 0 else (if i.val < 62 then (if i.val < 60 then 6 else 0) else 0)) else (if i.val <
    73 then (if i.val < 69 then 0 else (if i.val < 71 then 0 else (if i.val < 72 then 0 else
    -12))) else 0)) else (if i.val < 93 then (if i.val < 86 then 0 else (if i.val < 89 then 0
    else (if i.val < 91 then (if i.val < 90 then 0 else -4) else 0))) else (if i.val < 100 then
    0 else (if i.val < 103 then 0 else (if i.val < 105 then (if i.val < 104 then 0 else -4) else
    0)))))) else (if i.val < 161 then (if i.val < 134 then 0 else (if i.val < 147 then (if i.val
    < 140 then 0 else (if i.val < 143 then (if i.val < 141 then 0 else (if i.val < 142 then (-12
    / 5) else 0)) else (if i.val < 145 then 0 else (if i.val < 146 then (18 / 5) else 0)))) else
    (if i.val < 154 then (if i.val < 150 then (if i.val < 148 then (18 / 5) else 0) else (if
    i.val < 152 then (if i.val < 151 then 0 else (-12 / 5)) else 0)) else 0))) else (if i.val <
    188 then (if i.val < 174 then (if i.val < 167 then 0 else (if i.val < 170 then 0 else (if
    i.val < 172 then (if i.val < 171 then 0 else (-36 / 5)) else 0))) else (if i.val < 181 then
    (if i.val < 177 then (if i.val < 175 then 0 else (if i.val < 176 then 0 else (-36 / 5)))
    else 0) else 0)) else 0))) else (if i.val < 322 then (if i.val < 268 then (if i.val < 241
    then (if i.val < 228 then (if i.val < 221 then 0 else (if i.val < 224 then (if i.val < 222
    then (-12 / 5) else 0) else (if i.val < 226 then 0 else (if i.val < 227 then 0 else (18 /
    5))))) else 0) else (if i.val < 254 then (if i.val < 247 then 0 else (if i.val < 250 then 0
    else (if i.val < 252 then (if i.val < 251 then 0 else (-12 / 5)) else 0))) else (if i.val <
    261 then (if i.val < 257 then 0 else (if i.val < 259 then (if i.val < 258 then 0 else (18 /
    5)) else 0)) else (if i.val < 264 then (if i.val < 262 then 0 else (if i.val < 263 then (-12
    / 5) else 0)) else (if i.val < 266 then 0 else (if i.val < 267 then 0 else (18 / 5)))))))
    else (if i.val < 295 then (if i.val < 281 then (if i.val < 274 then 0 else (if i.val < 277
    then (if i.val < 275 then (-36 / 5) else 0) else (if i.val < 279 then (if i.val < 278 then 0
    else (-12 / 5)) else 0))) else (if i.val < 288 then (if i.val < 284 then (if i.val < 282
    then 0 else (if i.val < 283 then 0 else (24 / 5))) else (if i.val < 286 then 0 else (if
    i.val < 287 then 0 else (-12 / 5)))) else (if i.val < 291 then (if i.val < 289 then (-12 /
    5) else 0) else (if i.val < 293 then (if i.val < 292 then 0 else (12 / 5)) else 0)))) else
    (if i.val < 308 then (if i.val < 301 then (if i.val < 298 then 0 else (if i.val < 299 then 0
    else (if i.val < 300 then (24 / 5) else 0))) else (if i.val < 304 then (if i.val < 302 then
    (24 / 5) else 0) else (if i.val < 306 then (if i.val < 305 then 0 else (-12 / 5)) else 0)))
    else (if i.val < 315 then (if i.val < 311 then (if i.val < 309 then 0 else (if i.val < 310
    then (24 / 5) else 0)) else (if i.val < 313 then 0 else (if i.val < 314 then 0 else (-12 /
    5)))) else (if i.val < 318 then (if i.val < 316 then 0 else (if i.val < 317 then 0 else (-12
    / 5))) else (if i.val < 320 then 0 else (if i.val < 321 then 0 else (6 / 5)))))))) else (if
    i.val < 376 then (if i.val < 349 then (if i.val < 335 then (if i.val < 328 then 0 else (if
    i.val < 331 then (if i.val < 329 then (-36 / 5) else 0) else (if i.val < 333 then (if i.val
    < 332 then (-12 / 5) else 0) else 0))) else (if i.val < 342 then (if i.val < 338 then 0 else
    (if i.val < 340 then (if i.val < 339 then (-36 / 5) else 0) else 0)) else (if i.val < 345
    then (if i.val < 343 then 0 else (-36 / 5)) else (if i.val < 347 then 0 else (if i.val < 348
    then (-36 / 5) else 0))))) else (if i.val < 362 then (if i.val < 355 then (if i.val < 352
    then (if i.val < 350 then 0 else (if i.val < 351 then (-12 / 5) else 0)) else 0) else (if
    i.val < 358 then (if i.val < 356 then 0 else (if i.val < 357 then 0 else (-36 / 5))) else
    (if i.val < 360 then 0 else (if i.val < 361 then 0 else (24 / 5))))) else (if i.val < 369
    then (if i.val < 365 then 0 else (if i.val < 367 then 0 else (if i.val < 368 then 0 else
    (-12 / 5)))) else (if i.val < 372 then 0 else (if i.val < 374 then 0 else (if i.val < 375
    then 0 else (24 / 5))))))) else 0))) else (if i.val < 645 then (if i.val < 537 then (if
    i.val < 483 then 0 else (if i.val < 510 then (if i.val < 496 then 0 else (if i.val < 503
    then 0 else (if i.val < 506 then (if i.val < 504 then 0 else (if i.val < 505 then 0 else (-1
    / 10))) else 0))) else (if i.val < 523 then (if i.val < 516 then (if i.val < 513 then (if
    i.val < 511 then 0 else (if i.val < 512 then (-3 / 10) else 0)) else 0) else 0) else (if
    i.val < 530 then (if i.val < 526 then (if i.val < 524 then 0 else (if i.val < 525 then 0
    else (-1 / 10))) else 0) else (if i.val < 533 then 0 else (if i.val < 535 then 0 else (if
    i.val < 536 then 0 else (-1 / 10)))))))) else (if i.val < 591 then (if i.val < 564 then (if
    i.val < 550 then (if i.val < 543 then (if i.val < 540 then 0 else (if i.val < 541 then 0
    else (if i.val < 542 then (-1 / 10) else 0))) else (if i.val < 546 then 0 else (if i.val <
    548 then (if i.val < 547 then (-3 / 10) else 0) else 0))) else (if i.val < 557 then (if
    i.val < 553 then (if i.val < 551 then (-3 / 5) else 0) else (if i.val < 555 then 0 else (if
    i.val < 556 then (1 / 5) else 0))) else (if i.val < 560 then 0 else (if i.val < 562 then (if
    i.val < 561 then (-3 / 5) else 0) else (if i.val < 563 then (-3 / 5) else 0))))) else (if
    i.val < 577 then (if i.val < 570 then (if i.val < 567 then (if i.val < 565 then 0 else (if
    i.val < 566 then 0 else (3 / 5))) else 0) else (if i.val < 573 then 0 else (if i.val < 575
    then (if i.val < 574 then (1 / 5) else 0) else (if i.val < 576 then (1 / 5) else 0)))) else
    (if i.val < 584 then (if i.val < 580 then (if i.val < 578 then 0 else (if i.val < 579 then 0
    else (-3 / 5))) else 0) else (if i.val < 587 then (if i.val < 585 then (1 / 5) else 0) else
    (if i.val < 589 then 0 else (if i.val < 590 then (-3 / 5) else 0)))))) else (if i.val < 618
    then (if i.val < 604 then (if i.val < 597 then (if i.val < 594 then (if i.val < 592 then 0
    else (if i.val < 593 then (-3 / 5) else 0)) else (if i.val < 595 then 0 else (if i.val < 596
    then 0 else (3 / 5)))) else (if i.val < 600 then 0 else (if i.val < 602 then (if i.val < 601
    then (-1 / 20) else 0) else 0))) else (if i.val < 611 then (if i.val < 607 then (if i.val <
    605 then 0 else (3 / 20)) else (if i.val < 609 then 0 else (if i.val < 610 then 0 else (-3 /
    20)))) else (if i.val < 614 then 0 else (if i.val < 616 then 0 else (if i.val < 617 then (3
    / 20) else 0))))) else (if i.val < 631 then (if i.val < 624 then (if i.val < 621 then 0 else
    (if i.val < 622 then (-3 / 20) else (if i.val < 623 then 0 else (-3 / 20)))) else (if i.val
    < 627 then 0 else (if i.val < 629 then (if i.val < 628 then (1 / 20) else 0) else 0))) else
    (if i.val < 638 then (if i.val < 634 then (if i.val < 632 then 0 else (if i.val < 633 then
    (-1 / 20) else 0)) else (if i.val < 636 then 0 else (if i.val < 637 then 0 else (3 / 20))))
    else (if i.val < 641 then (if i.val < 639 then 0 else (if i.val < 640 then (3 / 20) else 0))
    else (if i.val < 643 then 0 else (if i.val < 644 then (-3 / 20) else 0)))))))) else (if
    i.val < 752 then (if i.val < 698 then (if i.val < 671 then (if i.val < 658 then (if i.val <
    651 then (if i.val < 648 then 0 else (if i.val < 649 then (3 / 20) else 0)) else (if i.val <
    654 then (if i.val < 652 then 0 else (if i.val < 653 then 0 else (-3 / 20))) else (if i.val
    < 656 then 0 else (if i.val < 657 then (-3 / 20) else 0)))) else (if i.val < 664 then (if
    i.val < 661 then (if i.val < 659 then 0 else (if i.val < 660 then 0 else (1 / 20))) else 0)
    else 0)) else 0) else 0) else (if i.val < 806 then 0 else (if i.val < 833 then (if i.val <
    819 then (if i.val < 812 then 0 else (if i.val < 815 then 0 else (if i.val < 817 then (if
    i.val < 816 then 0 else -6) else 0))) else (if i.val < 826 then 0 else (if i.val < 829 then
    0 else (if i.val < 831 then (if i.val < 830 then 6 else 0) else (if i.val < 832 then -4 else
    0))))) else (if i.val < 846 then (if i.val < 839 then 0 else (if i.val < 842 then (if i.val
    < 840 then 0 else (if i.val < 841 then (24 / 5) else 0)) else 0)) else (if i.val < 853 then
    (if i.val < 849 then 0 else (if i.val < 851 then 0 else (if i.val < 852 then (-36 / 5) else
    0))) else (if i.val < 856 then (if i.val < 854 then 0 else (if i.val < 855 then 0 else (1 /
    5))) else 0))))))))

/-- Kernel arithmetic adds every signed coefficient at its proposed destination. -/
theorem raw2_checked : StrataOperation.recordCoordinates records2 = raw2 := by
  decide +kernel

/-- Consolidation of the actual signed pullback contribution. -/
theorem coordinates2_checked :
    CotangentCombination.recordCoordinates (CotangentCombination.dimensionRecords
      L24InitialHints.columnIndex (Pi.single 2 1) L24Initial.pullback) = raw2 := by
  rw [records2_checked]
  simpa only [CotangentCombination.recordCoordinates, Multiset.map_coe, Multiset.sum_coe,
    StrataOperation.recordCoordinates_eq_sum] using raw2_checked

set_option maxHeartbeats 800000 in
-- Elaborating the 306 exact records exceeds the default declaration budget.
/-- Proposed records for the psi-3 term; no multiplicity is removed. -/
def records3 : List (Fin 860 × ℚ) :=
  ([(0, 0), (0, 0), (91, -2), (0, 0), (0, 0), (91, -2), (0, 0), (0, 0), (100, -2), (0, 0), (833,
    -2), (0, 0), (0, 0), (0, 0), (100, -2), (0, 0), (833, -2), (0, 0), (73, -2), (12, 2), (47,
    2), (73, -2), (12, 2), (47, 2), (73, -2), (12, 2), (47, 2), (73, -2), (12, 2), (47, 2), (73,
    -2), (12, 2), (47, 2), (73, -2), (12, 2), (47, 2), (0, 0), (0, 0), (27, 3), (0, 0), (0, 0),
    (27, 3), (0, 0), (0, 0), (826, 3), (0, 0), (9, 3), (42, 3), (0, 0), (0, 0), (826, 3)] : List
    (Fin 860 × ℚ)) ++ ([(0, 0), (9, 3), (42, 3), (0, 0), (0, 0), (28, -3), (0, 0), (0, 0), (28,
    -3), (0, 0), (0, 0), (36, -3), (66, 3), (818, -3), (43, -3), (0, 0), (0, 0), (36, -3), (66,
    3), (818, -3), (43, -3), (293, (1 / 5)), (322, (1 / 5)), (293, (1 / 5)), (293, (1 / 5)),
    (322, (1 / 5)), (293, (1 / 5)), (293, (1 / 5)), (322, (1 / 5)), (293, (1 / 5)), (293, (1 /
    5)), (322, (1 / 5)), (293, (1 / 5)), (293, (1 / 5)), (322, (1 / 5)), (293, (1 / 5)), (293,
    (1 / 5)), (322, (1 / 5)), (293, (1 / 5)), (329, (-6 / 5)), (318, (-6 / 5)), (290, (-6 / 5)),
    (352, (-6 / 5)), (313, (-6 / 5)), (285, (-6 / 5)), (329, (-6 / 5)), (318, (-6 / 5)), (290,
    (-6 / 5)), (352, (-6 / 5)), (313, (-6 / 5)), (285, (-6 / 5))] : List (Fin 860 × ℚ)) ++
    ([(369, (-6 / 5)), (306, (-6 / 5)), (279, (-6 / 5)), (369, (-6 / 5)), (306, (-6 / 5)), (279,
    (-6 / 5)), (362, (12 / 5)), (310, (12 / 5)), (284, (12 / 5)), (362, (12 / 5)), (310, (12 /
    5)), (284, (12 / 5)), (372, (12 / 5)), (303, (12 / 5)), (842, (12 / 5)), (0, 0), (297, (12 /
    5)), (0, 0), (372, (12 / 5)), (303, (12 / 5)), (842, (12 / 5)), (0, 0), (297, (12 / 5)), (0,
    0), (323, (-18 / 5)), (336, (-18 / 5)), (853, (-18 / 5)), (0, 0), (359, (-18 / 5)), (0, 0),
    (326, (-18 / 5)), (340, (-18 / 5)), (349, (-18 / 5)), (349, (-18 / 5)), (340, (-18 / 5)),
    (326, (-18 / 5)), (0, 0), (359, (-18 / 5)), (0, 0), (853, (-18 / 5)), (336, (-18 / 5)),
    (323, (-18 / 5)), (177, (-6 / 5)), (172, (-6 / 5)), (275, (-6 / 5)), (177, (-6 / 5)), (172,
    (-6 / 5)), (275, (-6 / 5)), (177, (-6 / 5)), (172, (-6 / 5)), (275, (-6 / 5))] : List (Fin
    860 × ℚ)) ++ ([(177, (-6 / 5)), (172, (-6 / 5)), (275, (-6 / 5)), (177, (-6 / 5)), (172, (-6
    / 5)), (275, (-6 / 5)), (177, (-6 / 5)), (172, (-6 / 5)), (275, (-6 / 5)), (0, 0), (0, 0),
    (228, (9 / 5)), (0, 0), (0, 0), (228, (9 / 5)), (0, 0), (0, 0), (255, (9 / 5)), (160, (9 /
    5)), (162, (9 / 5)), (270, (9 / 5)), (0, 0), (0, 0), (255, (9 / 5)), (160, (9 / 5)), (162,
    (9 / 5)), (270, (9 / 5)), (0, 0), (0, 0), (222, (-6 / 5)), (0, 0), (0, 0), (222, (-6 / 5)),
    (0, 0), (0, 0), (250, (-6 / 5)), (166, (-6 / 5)), (156, (-6 / 5)), (263, (-6 / 5)), (0, 0),
    (0, 0), (250, (-6 / 5)), (166, (-6 / 5)), (156, (-6 / 5)), (263, (-6 / 5)), (661, (1 /
    120)), (628, (1 / 120)), (661, (1 / 120)), (628, (1 / 120)), (661, (1 / 120)), (628, (1 /
    120))] : List (Fin 860 × ℚ)) ++ ([(661, (1 / 120)), (628, (1 / 120)), (661, (1 / 120)),
    (628, (1 / 120)), (661, (1 / 120)), (628, (1 / 120)), (657, (-3 / 40)), (625, (-3 / 40)),
    (652, (-3 / 40)), (619, (-3 / 40)), (657, (-3 / 40)), (625, (-3 / 40)), (652, (-3 / 40)),
    (619, (-3 / 40)), (644, (-3 / 40)), (611, (-3 / 40)), (644, (-3 / 40)), (611, (-3 / 40)),
    (649, (3 / 40)), (617, (3 / 40)), (649, (3 / 40)), (617, (3 / 40)), (641, (3 / 40)), (609,
    (3 / 40)), (635, (3 / 40)), (602, (3 / 40)), (641, (3 / 40)), (609, (3 / 40)), (635, (3 /
    40)), (602, (3 / 40)), (633, (-1 / 120)), (601, (-1 / 120)), (633, (-1 / 120)), (601, (-1 /
    120)), (633, (-1 / 120)), (601, (-1 / 120)), (633, (-1 / 120)), (601, (-1 / 120)), (633, (-1
    / 120)), (601, (-1 / 120)), (633, (-1 / 120)), (601, (-1 / 120)), (597, (1 / 10)), (567, (1
    / 10)), (597, (1 / 10)), (567, (1 / 10)), (597, (1 / 10)), (567, (1 / 10)), (597, (1 / 10)),
    (567, (1 / 10)), (597, (1 / 10))] : List (Fin 860 × ℚ)) ++ ([(567, (1 / 10)), (597, (1 /
    10)), (567, (1 / 10)), (593, (-3 / 10)), (564, (-3 / 10)), (588, (-3 / 10)), (558, (-3 /
    10)), (593, (-3 / 10)), (564, (-3 / 10)), (588, (-3 / 10)), (558, (-3 / 10)), (580, (-3 /
    10)), (551, (-3 / 10)), (580, (-3 / 10)), (551, (-3 / 10)), (585, (1 / 10)), (556, (1 /
    10)), (585, (1 / 10)), (556, (1 / 10)), (577, (1 / 10)), (857, (1 / 10)), (571, (1 / 10)),
    (0, 0), (577, (1 / 10)), (857, (1 / 10)), (571, (1 / 10)), (0, 0), (512, (-1 / 20)), (547,
    (-1 / 20)), (512, (-1 / 20)), (547, (-1 / 20)), (512, (-1 / 20)), (547, (-1 / 20)), (512,
    (-1 / 20)), (547, (-1 / 20)), (512, (-1 / 20)), (547, (-1 / 20)), (512, (-1 / 20)), (547,
    (-1 / 20)), (0, 0), (526, (-1 / 20)), (0, 0), (526, (-1 / 20)), (0, 0), (535, (-1 / 20)),
    (508, (-1 / 20)), (542, (-1 / 20)), (0, 0), (535, (-1 / 20)), (508, (-1 / 20)), (542, (-1 /
    20))] : List (Fin 860 × ℚ))

/-- The records equal the actual dimension-pruned signed pullback computation. -/
theorem records3_checked : CotangentCombination.dimensionRecords
    L24InitialHints.columnIndex (Pi.single 3 1) L24Initial.pullback =
    (records3 : Multiset (Fin 860 × ℚ)) := by
  decide +kernel

/-- Proposed consolidated coefficients, before the weighted marking average. -/
def raw3 : Coordinates 860 :=
  fun i ↦ (if i.val < 430 then (if i.val < 215 then (if i.val < 107 then (if i.val < 53 then (if
    i.val < 26 then (if i.val < 13 then (if i.val < 6 then 0 else (if i.val < 9 then 0 else (if
    i.val < 11 then (if i.val < 10 then 6 else 0) else (if i.val < 12 then 0 else 12)))) else 0)
    else (if i.val < 39 then (if i.val < 32 then (if i.val < 29 then (if i.val < 27 then 0 else
    (if i.val < 28 then 6 else -6)) else 0) else (if i.val < 35 then 0 else (if i.val < 37 then
    (if i.val < 36 then 0 else -6) else 0))) else (if i.val < 46 then (if i.val < 42 then 0 else
    (if i.val < 44 then (if i.val < 43 then 6 else -6) else 0)) else (if i.val < 49 then (if
    i.val < 47 then 0 else (if i.val < 48 then 12 else 0)) else 0)))) else (if i.val < 80 then
    (if i.val < 66 then 0 else (if i.val < 73 then (if i.val < 69 then (if i.val < 67 then 6
    else 0) else 0) else (if i.val < 76 then (if i.val < 74 then -12 else 0) else 0))) else (if
    i.val < 93 then (if i.val < 86 then 0 else (if i.val < 89 then 0 else (if i.val < 91 then 0
    else (if i.val < 92 then -4 else 0)))) else (if i.val < 100 then 0 else (if i.val < 103 then
    (if i.val < 101 then -4 else 0) else 0))))) else (if i.val < 161 then (if i.val < 134 then 0
    else (if i.val < 147 then 0 else (if i.val < 154 then 0 else (if i.val < 157 then (if i.val
    < 155 then 0 else (if i.val < 156 then 0 else (-12 / 5))) else (if i.val < 159 then 0 else
    (if i.val < 160 then 0 else (18 / 5))))))) else (if i.val < 188 then (if i.val < 174 then
    (if i.val < 167 then (if i.val < 164 then (if i.val < 162 then 0 else (if i.val < 163 then
    (18 / 5) else 0)) else (if i.val < 165 then 0 else (if i.val < 166 then 0 else (-12 / 5))))
    else (if i.val < 170 then 0 else (if i.val < 172 then 0 else (if i.val < 173 then (-36 / 5)
    else 0)))) else (if i.val < 181 then (if i.val < 177 then 0 else (if i.val < 179 then (if
    i.val < 178 then (-36 / 5) else 0) else 0)) else 0)) else 0))) else (if i.val < 322 then (if
    i.val < 268 then (if i.val < 241 then (if i.val < 228 then (if i.val < 221 then 0 else (if
    i.val < 224 then (if i.val < 222 then 0 else (if i.val < 223 then (-12 / 5) else 0)) else
    0)) else (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then (18 / 5) else 0)
    else 0) else 0)) else (if i.val < 254 then (if i.val < 247 then 0 else (if i.val < 250 then
    0 else (if i.val < 252 then (if i.val < 251 then (-12 / 5) else 0) else 0))) else (if i.val
    < 261 then (if i.val < 257 then (if i.val < 255 then 0 else (if i.val < 256 then (18 / 5)
    else 0)) else 0) else (if i.val < 264 then (if i.val < 262 then 0 else (if i.val < 263 then
    0 else (-12 / 5))) else 0)))) else (if i.val < 295 then (if i.val < 281 then (if i.val < 274
    then (if i.val < 271 then (if i.val < 269 then 0 else (if i.val < 270 then 0 else (18 / 5)))
    else 0) else (if i.val < 277 then (if i.val < 275 then 0 else (if i.val < 276 then (-36 / 5)
    else 0)) else (if i.val < 279 then 0 else (if i.val < 280 then (-12 / 5) else 0)))) else (if
    i.val < 288 then (if i.val < 284 then 0 else (if i.val < 286 then (if i.val < 285 then (24 /
    5) else (-12 / 5)) else 0)) else (if i.val < 291 then (if i.val < 289 then 0 else (if i.val
    < 290 then 0 else (-12 / 5))) else (if i.val < 293 then 0 else (if i.val < 294 then (12 / 5)
    else 0))))) else (if i.val < 308 then (if i.val < 301 then (if i.val < 298 then (if i.val <
    296 then 0 else (if i.val < 297 then 0 else (24 / 5))) else 0) else (if i.val < 304 then (if
    i.val < 302 then 0 else (if i.val < 303 then 0 else (24 / 5))) else (if i.val < 306 then 0
    else (if i.val < 307 then (-12 / 5) else 0)))) else (if i.val < 315 then (if i.val < 311
    then (if i.val < 309 then 0 else (if i.val < 310 then 0 else (24 / 5))) else (if i.val < 313
    then 0 else (if i.val < 314 then (-12 / 5) else 0))) else (if i.val < 318 then 0 else (if
    i.val < 320 then (if i.val < 319 then (-12 / 5) else 0) else 0)))))) else (if i.val < 376
    then (if i.val < 349 then (if i.val < 335 then (if i.val < 328 then (if i.val < 325 then (if
    i.val < 323 then (6 / 5) else (if i.val < 324 then (-36 / 5) else 0)) else (if i.val < 326
    then 0 else (if i.val < 327 then (-36 / 5) else 0))) else (if i.val < 331 then (if i.val <
    329 then 0 else (if i.val < 330 then (-12 / 5) else 0)) else 0)) else (if i.val < 342 then
    (if i.val < 338 then (if i.val < 336 then 0 else (if i.val < 337 then (-36 / 5) else 0))
    else (if i.val < 340 then 0 else (if i.val < 341 then (-36 / 5) else 0))) else 0)) else (if
    i.val < 362 then (if i.val < 355 then (if i.val < 352 then (if i.val < 350 then (-36 / 5)
    else 0) else (if i.val < 353 then (-12 / 5) else 0)) else (if i.val < 358 then 0 else (if
    i.val < 360 then (if i.val < 359 then 0 else (-36 / 5)) else 0))) else (if i.val < 369 then
    (if i.val < 365 then (if i.val < 363 then (24 / 5) else 0) else 0) else (if i.val < 372 then
    (if i.val < 370 then (-12 / 5) else 0) else (if i.val < 374 then (if i.val < 373 then (24 /
    5) else 0) else 0))))) else 0))) else (if i.val < 645 then (if i.val < 537 then (if i.val <
    483 then 0 else (if i.val < 510 then (if i.val < 496 then 0 else (if i.val < 503 then 0 else
    (if i.val < 506 then 0 else (if i.val < 508 then 0 else (if i.val < 509 then (-1 / 10) else
    0))))) else (if i.val < 523 then (if i.val < 516 then (if i.val < 513 then (if i.val < 511
    then 0 else (if i.val < 512 then 0 else (-3 / 10))) else 0) else 0) else (if i.val < 530
    then (if i.val < 526 then 0 else (if i.val < 528 then (if i.val < 527 then (-1 / 10) else 0)
    else 0)) else (if i.val < 533 then 0 else (if i.val < 535 then 0 else (if i.val < 536 then
    (-1 / 10) else 0))))))) else (if i.val < 591 then (if i.val < 564 then (if i.val < 550 then
    (if i.val < 543 then (if i.val < 540 then 0 else (if i.val < 541 then 0 else (if i.val < 542
    then 0 else (-1 / 10)))) else (if i.val < 546 then 0 else (if i.val < 548 then (if i.val <
    547 then 0 else (-3 / 10)) else 0))) else (if i.val < 557 then (if i.val < 553 then (if
    i.val < 551 then 0 else (if i.val < 552 then (-3 / 5) else 0)) else (if i.val < 555 then 0
    else (if i.val < 556 then 0 else (1 / 5)))) else (if i.val < 560 then (if i.val < 558 then 0
    else (if i.val < 559 then (-3 / 5) else 0)) else 0))) else (if i.val < 577 then (if i.val <
    570 then (if i.val < 567 then (if i.val < 565 then (-3 / 5) else 0) else (if i.val < 568
    then (3 / 5) else 0)) else (if i.val < 573 then (if i.val < 571 then 0 else (if i.val < 572
    then (1 / 5) else 0)) else 0)) else (if i.val < 584 then (if i.val < 580 then (if i.val <
    578 then (1 / 5) else 0) else (if i.val < 582 then (if i.val < 581 then (-3 / 5) else 0)
    else 0)) else (if i.val < 587 then (if i.val < 585 then 0 else (if i.val < 586 then (1 / 5)
    else 0)) else (if i.val < 589 then (if i.val < 588 then 0 else (-3 / 5)) else 0))))) else
    (if i.val < 618 then (if i.val < 604 then (if i.val < 597 then (if i.val < 594 then (if
    i.val < 592 then 0 else (if i.val < 593 then 0 else (-3 / 5))) else 0) else (if i.val < 600
    then (if i.val < 598 then (3 / 5) else 0) else (if i.val < 602 then (if i.val < 601 then 0
    else (-1 / 20)) else (if i.val < 603 then (3 / 20) else 0)))) else (if i.val < 611 then (if
    i.val < 607 then 0 else (if i.val < 609 then 0 else (if i.val < 610 then (3 / 20) else 0)))
    else (if i.val < 614 then (if i.val < 612 then (-3 / 20) else 0) else (if i.val < 616 then 0
    else (if i.val < 617 then 0 else (3 / 20)))))) else (if i.val < 631 then (if i.val < 624
    then (if i.val < 621 then (if i.val < 619 then 0 else (if i.val < 620 then (-3 / 20) else
    0)) else 0) else (if i.val < 627 then (if i.val < 625 then 0 else (if i.val < 626 then (-3 /
    20) else 0)) else (if i.val < 629 then (if i.val < 628 then 0 else (1 / 20)) else 0))) else
    (if i.val < 638 then (if i.val < 634 then (if i.val < 632 then 0 else (if i.val < 633 then 0
    else (-1 / 20))) else (if i.val < 636 then (if i.val < 635 then 0 else (3 / 20)) else 0))
    else (if i.val < 641 then 0 else (if i.val < 643 then (if i.val < 642 then (3 / 20) else 0)
    else (if i.val < 644 then 0 else (-3 / 20))))))))) else (if i.val < 752 then (if i.val < 698
    then (if i.val < 671 then (if i.val < 658 then (if i.val < 651 then (if i.val < 648 then 0
    else (if i.val < 649 then 0 else (if i.val < 650 then (3 / 20) else 0))) else (if i.val <
    654 then (if i.val < 652 then 0 else (if i.val < 653 then (-3 / 20) else 0)) else (if i.val
    < 656 then 0 else (if i.val < 657 then 0 else (-3 / 20))))) else (if i.val < 664 then (if
    i.val < 661 then 0 else (if i.val < 662 then (1 / 20) else 0)) else 0)) else 0) else 0) else
    (if i.val < 806 then 0 else (if i.val < 833 then (if i.val < 819 then (if i.val < 812 then 0
    else (if i.val < 815 then 0 else (if i.val < 817 then 0 else (if i.val < 818 then 0 else
    -6)))) else (if i.val < 826 then 0 else (if i.val < 829 then (if i.val < 827 then 6 else 0)
    else 0))) else (if i.val < 846 then (if i.val < 839 then (if i.val < 836 then (if i.val <
    834 then -4 else 0) else 0) else (if i.val < 842 then 0 else (if i.val < 844 then (if i.val
    < 843 then (24 / 5) else 0) else 0))) else (if i.val < 853 then 0 else (if i.val < 856 then
    (if i.val < 854 then (-36 / 5) else 0) else (if i.val < 858 then (if i.val < 857 then 0 else
    (1 / 5)) else 0)))))))))

/-- Kernel arithmetic adds every signed coefficient at its proposed destination. -/
theorem raw3_checked : StrataOperation.recordCoordinates records3 = raw3 := by
  decide +kernel

/-- Consolidation of the actual signed pullback contribution. -/
theorem coordinates3_checked :
    CotangentCombination.recordCoordinates (CotangentCombination.dimensionRecords
      L24InitialHints.columnIndex (Pi.single 3 1) L24Initial.pullback) = raw3 := by
  rw [records3_checked]
  simpa only [CotangentCombination.recordCoordinates, Multiset.map_coe, Multiset.sum_coe,
    StrataOperation.recordCoordinates_eq_sum] using raw3_checked

/-- The four independently checked coordinate contributions. -/
def raw : Fin 4 → Coordinates 860 :=
  ![raw0, raw1, raw2, raw3]

/-- The actual computed coordinate vector, including all dimension-pruning markers. -/
theorem coordinates_checked (k : Fin 4) :
    CotangentCombination.recordCoordinates (CotangentCombination.dimensionRecords
      L24InitialHints.columnIndex (Pi.single k 1) L24Initial.pullback) = raw k := by
  fin_cases k
  · exact coordinates0_checked
  · exact coordinates1_checked
  · exact coordinates2_checked
  · exact coordinates3_checked

/-- Exact coefficients of the weighted BP expression before averaging. -/
def beforeAverageClaim : Coordinates 860 :=
  fun i ↦ (if i.val < 430 then (if i.val < 215 then (if i.val < 107 then (if i.val < 53 then (if
    i.val < 26 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then
    (-1 / 2) else (if i.val < 2 then (1 / 2) else (3 / 2))) else (if i.val < 4 then (-3 / 2)
    else (if i.val < 5 then 0 else (-1 / 2)))) else (if i.val < 9 then (if i.val < 7 then (1 /
    2) else (if i.val < 8 then 0 else (-1 / 2))) else (if i.val < 11 then (if i.val < 10 then (1
    / 2) else 0) else 1))) else (if i.val < 19 then (if i.val < 16 then (if i.val < 14 then 0
    else (if i.val < 15 then -1 else 0)) else 0) else (if i.val < 22 then 0 else (if i.val < 24
    then (if i.val < 23 then 0 else (-1 / 2)) else (1 / 2))))) else (if i.val < 39 then (if
    i.val < 32 then (if i.val < 29 then (if i.val < 27 then (-1 / 2) else (if i.val < 28 then (1
    / 2) else (-1 / 2))) else (if i.val < 30 then (3 / 2) else (if i.val < 31 then (-3 / 2) else
    0))) else (if i.val < 35 then (if i.val < 33 then 0 else (if i.val < 34 then 0 else (1 /
    2))) else (if i.val < 37 then (if i.val < 36 then (3 / 2) else (-1 / 2)) else (if i.val < 38
    then (1 / 2) else (-1 / 2))))) else (if i.val < 46 then (if i.val < 42 then (if i.val < 40
    then (1 / 2) else (if i.val < 41 then (3 / 2) else (-1 / 2))) else (if i.val < 44 then (if
    i.val < 43 then (1 / 2) else (-1 / 2)) else (if i.val < 45 then -1 else 3))) else (if i.val
    < 49 then (if i.val < 47 then 1 else (if i.val < 48 then 1 else (1 / 3))) else (if i.val <
    51 then (if i.val < 50 then 0 else (3 / 2)) else 0))))) else (if i.val < 80 then (if i.val <
    66 then (if i.val < 59 then (if i.val < 56 then (if i.val < 54 then 0 else (if i.val < 55
    then (1 / 3) else -1)) else (if i.val < 57 then 0 else (if i.val < 58 then (1 / 3) else 0)))
    else (if i.val < 62 then (if i.val < 60 then (1 / 2) else 0) else (if i.val < 64 then 0 else
    (if i.val < 65 then (1 / 3) else 0)))) else (if i.val < 73 then (if i.val < 69 then (if
    i.val < 67 then (1 / 2) else 0) else (if i.val < 71 then 0 else (if i.val < 72 then -3 else
    -1))) else (if i.val < 76 then (if i.val < 74 then -1 else 0) else 0))) else (if i.val < 93
    then (if i.val < 86 then 0 else (if i.val < 89 then 0 else (if i.val < 91 then (if i.val <
    90 then (1 / 3) else (-1 / 3)) else (if i.val < 92 then (-1 / 3) else 0)))) else (if i.val <
    100 then (if i.val < 96 then 0 else (if i.val < 98 then 0 else (if i.val < 99 then (1 / 3)
    else -1))) else (if i.val < 103 then (if i.val < 101 then (-1 / 3) else (if i.val < 102 then
    0 else (1 / 3))) else (if i.val < 105 then (if i.val < 104 then -1 else (-1 / 3)) else
    0)))))) else (if i.val < 161 then (if i.val < 134 then (if i.val < 120 then 0 else (if i.val
    < 127 then (if i.val < 123 then (if i.val < 121 then 0 else (if i.val < 122 then (1 / 5)
    else (-3 / 5))) else 0) else (if i.val < 130 then (if i.val < 128 then (-3 / 10) else (if
    i.val < 129 then (9 / 10) else 0)) else (if i.val < 132 then (if i.val < 131 then (9 / 10)
    else 0) else (if i.val < 133 then (-3 / 10) else 0))))) else (if i.val < 147 then (if i.val
    < 140 then (if i.val < 137 then (if i.val < 135 then 0 else (if i.val < 136 then (-3 / 5)
    else 0)) else (if i.val < 138 then 0 else (if i.val < 139 then (1 / 5) else 0))) else (if
    i.val < 143 then (if i.val < 141 then (1 / 5) else (if i.val < 142 then (-1 / 5) else 0))
    else (if i.val < 145 then (if i.val < 144 then 0 else (-3 / 10)) else (if i.val < 146 then
    (3 / 10) else 0)))) else (if i.val < 154 then (if i.val < 150 then (if i.val < 148 then (3 /
    10) else (if i.val < 149 then 0 else (-3 / 10))) else (if i.val < 152 then (if i.val < 151
    then 0 else (-1 / 5)) else (if i.val < 153 then 0 else (1 / 5)))) else (if i.val < 157 then
    (if i.val < 155 then 0 else (if i.val < 156 then (1 / 5) else (-1 / 5))) else (if i.val <
    159 then 0 else (if i.val < 160 then (-3 / 10) else (3 / 10))))))) else (if i.val < 188 then
    (if i.val < 174 then (if i.val < 167 then (if i.val < 164 then (if i.val < 162 then 0 else
    (if i.val < 163 then (3 / 10) else 0)) else (if i.val < 165 then (-3 / 10) else (if i.val <
    166 then 0 else (-1 / 5)))) else (if i.val < 170 then (if i.val < 168 then 0 else (if i.val
    < 169 then (1 / 5) else 0)) else (if i.val < 172 then (if i.val < 171 then (-9 / 5) else (-3
    / 5)) else (if i.val < 173 then (-3 / 5) else (3 / 5))))) else (if i.val < 181 then (if
    i.val < 177 then (if i.val < 175 then 0 else (if i.val < 176 then 0 else (-3 / 5))) else (if
    i.val < 179 then (if i.val < 178 then (-3 / 5) else 0) else (if i.val < 180 then 0 else (3 /
    5)))) else 0)) else 0))) else (if i.val < 322 then (if i.val < 268 then (if i.val < 241 then
    (if i.val < 228 then (if i.val < 221 then (if i.val < 218 then 0 else (if i.val < 219 then 0
    else (if i.val < 220 then 0 else (1 / 5)))) else (if i.val < 224 then (if i.val < 222 then
    (-1 / 5) else (if i.val < 223 then (-1 / 5) else (-3 / 5))) else (if i.val < 226 then 0 else
    (if i.val < 227 then (-3 / 10) else (3 / 10))))) else (if i.val < 234 then (if i.val < 231
    then (if i.val < 229 then (3 / 10) else 0) else (if i.val < 232 then (9 / 10) else 0)) else
    0)) else (if i.val < 254 then (if i.val < 247 then 0 else (if i.val < 250 then (if i.val <
    248 then 0 else (if i.val < 249 then (1 / 5) else (-3 / 5))) else (if i.val < 252 then (-1 /
    5) else 0))) else (if i.val < 261 then (if i.val < 257 then (if i.val < 255 then (-3 / 10)
    else (if i.val < 256 then (3 / 10) else 0)) else (if i.val < 259 then (if i.val < 258 then 0
    else (3 / 10)) else (if i.val < 260 then 0 else (1 / 5)))) else (if i.val < 264 then (if
    i.val < 262 then (-3 / 5) else (-1 / 5)) else (if i.val < 266 then 0 else (if i.val < 267
    then (-3 / 10) else (3 / 10))))))) else (if i.val < 295 then (if i.val < 281 then (if i.val
    < 274 then (if i.val < 271 then (if i.val < 269 then 0 else (if i.val < 270 then 0 else (3 /
    10))) else (if i.val < 272 then 0 else (if i.val < 273 then (3 / 5) else (-9 / 5)))) else
    (if i.val < 277 then (if i.val < 275 then (-3 / 5) else (if i.val < 276 then (-3 / 5) else
    (6 / 5))) else (if i.val < 279 then (if i.val < 278 then (6 / 5) else (-1 / 5)) else (if
    i.val < 280 then (-1 / 5) else (1 / 5))))) else (if i.val < 288 then (if i.val < 284 then
    (if i.val < 282 then (-3 / 5) else (if i.val < 283 then (-2 / 5) else (2 / 5))) else (if
    i.val < 286 then (if i.val < 285 then (2 / 5) else (-1 / 5)) else (if i.val < 287 then (1 /
    5) else (-1 / 5)))) else (if i.val < 291 then (if i.val < 289 then (-1 / 5) else (if i.val <
    290 then (1 / 5) else (-1 / 5))) else (if i.val < 293 then (if i.val < 292 then (3 / 5) else
    (1 / 5)) else (if i.val < 294 then (1 / 5) else (-1 / 5)))))) else (if i.val < 308 then (if
    i.val < 301 then (if i.val < 298 then (if i.val < 296 then 0 else (if i.val < 297 then (-2 /
    5) else (2 / 5))) else (if i.val < 299 then (6 / 5) else (if i.val < 300 then (2 / 5) else
    (-2 / 5)))) else (if i.val < 304 then (if i.val < 302 then (2 / 5) else (if i.val < 303 then
    (6 / 5) else (2 / 5))) else (if i.val < 306 then (if i.val < 305 then (1 / 5) else (-1 / 5))
    else (if i.val < 307 then (-1 / 5) else (-3 / 5))))) else (if i.val < 315 then (if i.val <
    311 then (if i.val < 309 then (-2 / 5) else (2 / 5)) else (if i.val < 313 then (if i.val <
    312 then (1 / 5) else (-3 / 5)) else (-1 / 5))) else (if i.val < 318 then (if i.val < 316
    then (1 / 5) else (if i.val < 317 then (-3 / 5) else (-1 / 5))) else (if i.val < 320 then
    (if i.val < 319 then (-1 / 5) else (-1 / 10)) else (if i.val < 321 then (3 / 10) else (1 /
    10)))))))) else (if i.val < 376 then (if i.val < 349 then (if i.val < 335 then (if i.val <
    328 then (if i.val < 325 then (if i.val < 323 then (1 / 10) else (if i.val < 324 then (-3 /
    5) else (3 / 5))) else (if i.val < 326 then (-9 / 5) else (if i.val < 327 then (-3 / 5) else
    (3 / 5)))) else (if i.val < 331 then (if i.val < 329 then (-3 / 5) else (if i.val < 330 then
    (-1 / 5) else (-3 / 5))) else (if i.val < 333 then (if i.val < 332 then (-1 / 5) else (1 /
    5)) else 0))) else (if i.val < 342 then (if i.val < 338 then (if i.val < 336 then 0 else (if
    i.val < 337 then (-3 / 5) else (3 / 5))) else (if i.val < 340 then (if i.val < 339 then (-3
    / 5) else (-9 / 5)) else (if i.val < 341 then (-3 / 5) else (3 / 5)))) else (if i.val < 345
    then (if i.val < 343 then (-9 / 5) else (-3 / 5)) else (if i.val < 347 then (if i.val < 346
    then (3 / 5) else (-9 / 5)) else (if i.val < 348 then (-3 / 5) else (3 / 5)))))) else (if
    i.val < 362 then (if i.val < 355 then (if i.val < 352 then (if i.val < 350 then (-3 / 5)
    else (if i.val < 351 then (-1 / 5) else (-3 / 5))) else (if i.val < 353 then (-1 / 5) else
    (if i.val < 354 then (1 / 5) else 0))) else (if i.val < 358 then (if i.val < 356 then 0 else
    (if i.val < 357 then 0 else (-3 / 5))) else (if i.val < 360 then (if i.val < 359 then (3 /
    5) else (-3 / 5)) else (if i.val < 361 then (-9 / 5) else (2 / 5))))) else (if i.val < 369
    then (if i.val < 365 then (if i.val < 363 then (2 / 5) else (if i.val < 364 then (-2 / 5)
    else 0)) else (if i.val < 367 then (-9 / 5) else (if i.val < 368 then (-3 / 5) else (-1 /
    5)))) else (if i.val < 372 then (if i.val < 370 then (-1 / 5) else (if i.val < 371 then (1 /
    5) else (6 / 5))) else (if i.val < 374 then (if i.val < 373 then (2 / 5) else (-2 / 5)) else
    (if i.val < 375 then (6 / 5) else (2 / 5))))))) else (if i.val < 403 then (if i.val < 389
    then (if i.val < 382 then (if i.val < 379 then (if i.val < 377 then (-2 / 5) else 0) else 0)
    else 0) else 0) else 0)))) else (if i.val < 645 then (if i.val < 537 then (if i.val < 483
    then 0 else (if i.val < 510 then (if i.val < 496 then 0 else (if i.val < 503 then (if i.val
    < 499 then 0 else (if i.val < 501 then (if i.val < 500 then 0 else (1 / 120)) else (if i.val
    < 502 then (-1 / 40) else 0))) else (if i.val < 506 then (if i.val < 504 then 0 else (if
    i.val < 505 then (1 / 120) else (-1 / 120))) else (if i.val < 508 then (if i.val < 507 then
    0 else (1 / 120)) else (if i.val < 509 then (-1 / 120) else 0))))) else (if i.val < 523 then
    (if i.val < 516 then (if i.val < 513 then (if i.val < 511 then (-3 / 40) else (-1 / 40))
    else (if i.val < 514 then (1 / 40) else 0)) else 0) else (if i.val < 530 then (if i.val <
    526 then (if i.val < 524 then 0 else (if i.val < 525 then (1 / 120) else (-1 / 120))) else
    (if i.val < 528 then (if i.val < 527 then (-1 / 120) else (-1 / 40)) else 0)) else (if i.val
    < 533 then 0 else (if i.val < 535 then (if i.val < 534 then (1 / 120) else (-1 / 40)) else
    (-1 / 120))))))) else (if i.val < 591 then (if i.val < 564 then (if i.val < 550 then (if
    i.val < 543 then (if i.val < 540 then (if i.val < 538 then 0 else (if i.val < 539 then 0
    else (1 / 120))) else (if i.val < 541 then (-1 / 40) else (-1 / 120))) else (if i.val < 546
    then (if i.val < 544 then 0 else (if i.val < 545 then (1 / 40) else (-3 / 40))) else (if
    i.val < 548 then (-1 / 40) else (1 / 20)))) else (if i.val < 557 then (if i.val < 553 then
    (if i.val < 551 then (-1 / 20) else (if i.val < 552 then (-1 / 20) else (1 / 20))) else (if
    i.val < 555 then (if i.val < 554 then (-3 / 20) else (-1 / 60)) else (1 / 60))) else (if
    i.val < 560 then (if i.val < 558 then (-3 / 20) else (if i.val < 559 then (-1 / 20) else (1
    / 20))) else (if i.val < 562 then (if i.val < 561 then (-1 / 20) else (-3 / 20)) else (if
    i.val < 563 then (-1 / 20) else (1 / 20)))))) else (if i.val < 577 then (if i.val < 570 then
    (if i.val < 567 then (if i.val < 565 then (-1 / 20) else (if i.val < 566 then (3 / 20) else
    (1 / 20))) else (if i.val < 568 then (1 / 20) else (if i.val < 569 then (-1 / 20) else 0)))
    else (if i.val < 573 then (if i.val < 571 then (-1 / 60) else (if i.val < 572 then (1 / 60)
    else (1 / 20))) else (if i.val < 575 then (if i.val < 574 then (1 / 60) else (-1 / 60)) else
    (if i.val < 576 then (1 / 60) else (1 / 20))))) else (if i.val < 584 then (if i.val < 580
    then (if i.val < 578 then (1 / 60) else (if i.val < 579 then (1 / 20) else (-1 / 20))) else
    (if i.val < 582 then (if i.val < 581 then (-1 / 20) else (-3 / 20)) else (if i.val < 583
    then (-1 / 60) else (1 / 20)))) else (if i.val < 587 then (if i.val < 585 then (1 / 60) else
    (if i.val < 586 then (1 / 60) else (1 / 20))) else (if i.val < 589 then (if i.val < 588 then
    (-3 / 20) else (-1 / 20)) else (if i.val < 590 then (-1 / 20) else (1 / 20))))))) else (if
    i.val < 618 then (if i.val < 604 then (if i.val < 597 then (if i.val < 594 then (if i.val <
    592 then (-3 / 20) else (-1 / 20)) else (if i.val < 595 then (-1 / 20) else (if i.val < 596
    then (3 / 20) else (1 / 20)))) else (if i.val < 600 then (if i.val < 598 then (1 / 20) else
    (if i.val < 599 then (1 / 240) else (-1 / 80))) else (if i.val < 602 then (-1 / 240) else
    (if i.val < 603 then (1 / 80) else (-1 / 80))))) else (if i.val < 611 then (if i.val < 607
    then (if i.val < 605 then (3 / 80) else (1 / 80)) else (if i.val < 609 then (if i.val < 608
    then (-1 / 80) else (3 / 80)) else (if i.val < 610 then (1 / 80) else (-1 / 80)))) else (if
    i.val < 614 then (if i.val < 612 then (-1 / 80) else (if i.val < 613 then (1 / 80) else (-3
    / 80))) else (if i.val < 616 then (if i.val < 615 then (3 / 80) else (-1 / 80)) else (1 /
    80))))) else (if i.val < 631 then (if i.val < 624 then (if i.val < 621 then (if i.val < 619
    then (-3 / 80) else (if i.val < 620 then (-1 / 80) else (1 / 80))) else (if i.val < 622 then
    (-1 / 80) else (if i.val < 623 then (-3 / 80) else (-1 / 80)))) else (if i.val < 627 then
    (if i.val < 625 then (1 / 80) else (if i.val < 626 then (-1 / 80) else (1 / 80))) else (if
    i.val < 629 then (1 / 240) else (if i.val < 630 then (-1 / 240) else (1 / 240))))) else (if
    i.val < 638 then (if i.val < 634 then (if i.val < 632 then (-1 / 80) else (-1 / 240)) else
    (if i.val < 636 then (if i.val < 635 then (-1 / 80) else (1 / 80)) else (if i.val < 637 then
    (3 / 80) else (1 / 80)))) else (if i.val < 641 then (if i.val < 639 then (-1 / 80) else (if
    i.val < 640 then (1 / 80) else (3 / 80))) else (if i.val < 643 then (1 / 80) else (-1 /
    80)))))))) else (if i.val < 752 then (if i.val < 698 then (if i.val < 671 then (if i.val <
    658 then (if i.val < 651 then (if i.val < 648 then (if i.val < 646 then (-3 / 80) else (if
    i.val < 647 then (-1 / 80) else (3 / 80))) else (1 / 80)) else (if i.val < 654 then (if
    i.val < 652 then (-3 / 80) else (-1 / 80)) else (if i.val < 656 then (if i.val < 655 then (1
    / 80) else (-3 / 80)) else (-1 / 80)))) else (if i.val < 664 then (if i.val < 661 then (if
    i.val < 659 then (-1 / 240) else (if i.val < 660 then (1 / 80) else (1 / 240))) else (if
    i.val < 662 then (1 / 240) else 0)) else 0)) else 0) else 0) else (if i.val < 806 then 0
    else (if i.val < 833 then (if i.val < 819 then (if i.val < 812 then 0 else (if i.val < 815
    then 0 else (if i.val < 817 then (if i.val < 816 then (1 / 2) else (-1 / 2)) else (if i.val
    < 818 then (1 / 2) else (-1 / 2))))) else (if i.val < 826 then (if i.val < 822 then (if
    i.val < 820 then 3 else 0) else (if i.val < 824 then 0 else (if i.val < 825 then (-1 / 2)
    else (-3 / 2)))) else (if i.val < 829 then (if i.val < 827 then (1 / 2) else (if i.val < 828
    then (-1 / 2) else (-3 / 2))) else (if i.val < 831 then (if i.val < 830 then (1 / 2) else (1
    / 3)) else (if i.val < 832 then (-1 / 3) else (1 / 3)))))) else (if i.val < 846 then (if
    i.val < 839 then (if i.val < 836 then (if i.val < 834 then (-1 / 3) else 0) else (if i.val <
    837 then (-9 / 5) else (9 / 10))) else (if i.val < 842 then (if i.val < 840 then (-2 / 5)
    else (if i.val < 841 then (2 / 5) else (-2 / 5))) else (if i.val < 844 then (if i.val < 843
    then (2 / 5) else (-3 / 5)) else (if i.val < 845 then (-3 / 5) else 0)))) else (if i.val <
    853 then (if i.val < 849 then (if i.val < 847 then 0 else (if i.val < 848 then (6 / 5) else
    0)) else (if i.val < 851 then (if i.val < 850 then 0 else (3 / 5)) else (if i.val < 852 then
    (-3 / 5) else (3 / 5)))) else (if i.val < 856 then (if i.val < 854 then (-3 / 5) else (if
    i.val < 855 then (-1 / 60) else (1 / 60))) else (if i.val < 858 then (if i.val < 857 then
    (-1 / 60) else (1 / 60)) else 0)))))))))

/-- All four cotangent contributions retain the original factor one twelfth. -/
theorem beforeAverage_checked :
    (1 / 12 : ℚ) • (∑ k : Fin 4, L24Initial.psiWeights k • raw k) = beforeAverageClaim := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero,
    L24Initial.psiWeights, raw, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  revert j
  decide +kernel

/-- Averaging cancels every auxiliary coefficient and recovers the held initial row. -/
theorem initial_checked : L24InitialGraphs.averageCoordinates beforeAverageClaim =
    L24InitialGraphs.extend L24CorrectionsReplay.initialClaim := by
  decide +kernel

/-- All signed multiplicities from the 120 original BP assignments survive. -/
theorem pullback_size : L24Initial.pullback.card = 306 := by
  decide +kernel

/-- Exactly 198 of the four weighted collections have a component dimension excess. -/
theorem pruned_count : (∑ k : Fin 4, (L24Initial.pullback.filter fun t ↦
    t.2.expression.exceedsComponentDimension t.2.decoration (Pi.single k 1) = true).card) =
    198 := by
  decide +kernel

end AxiomaticGW.L24InitialReplay
