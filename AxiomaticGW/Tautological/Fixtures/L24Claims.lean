/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.RelationCertificate



/-!
# Held L24 coordinate claims

Input SHA256: 227cd365a71aa1377c2b6c79c5a15b3217edbaf348cab6bcc8f4ab2c543cebe7
These are coefficient data only; L24CorrectionsReplay checks the complete assembly.
The initial BP coordinate claim is separate and requires its own graph replay.
-/

@[expose] public section

namespace AxiomaticGW.L24CorrectionsReplay
open RelationCertificate

set_option maxRecDepth 20000

/-- Incoming exact raw coordinates; validity is checked separately. -/
def initialClaim : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then
    (-1 / 6) else (if i.val < 2 then (1 / 6) else (1 / 2))) else (if i.val < 4 then (-1 / 2)
    else (if i.val < 5 then (1 / 6) else (-1 / 3)))) else (if i.val < 9 then (if i.val < 7 then
    (1 / 6) else (if i.val < 8 then (1 / 6) else (-1 / 3))) else (if i.val < 10 then (1 / 6)
    else (if i.val < 11 then 1 else (1 / 3))))) else (if i.val < 18 then (if i.val < 15 then (if
    i.val < 13 then (1 / 3) else (if i.val < 14 then (1 / 3) else (-2 / 3))) else (if i.val < 16
    then (1 / 2) else (if i.val < 17 then (-1 / 6) else (-1 / 2)))) else (if i.val < 21 then (if
    i.val < 19 then (1 / 6) else (if i.val < 20 then (1 / 2) else (-1 / 6))) else (if i.val < 23
    then (if i.val < 22 then (-1 / 2) else (1 / 6)) else (if i.val < 24 then (1 / 6) else (-1 /
    6)))))) else (if i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then
    (1 / 6) else (if i.val < 27 then (-1 / 6) else (1 / 6))) else (if i.val < 29 then (-1 / 6)
    else (if i.val < 30 then (3 / 2) else (-3 / 2)))) else (if i.val < 34 then (if i.val < 32
    then (1 / 6) else (if i.val < 33 then (-1 / 3) else (1 / 6))) else (if i.val < 35 then (1 /
    3) else (if i.val < 36 then 1 else (1 / 3))))) else (if i.val < 43 then (if i.val < 40 then
    (if i.val < 38 then (1 / 3) else (if i.val < 39 then (-2 / 3) else (1 / 3))) else (if i.val
    < 41 then 1 else (1 / 3))) else (if i.val < 46 then (if i.val < 44 then (-2 / 3) else (if
    i.val < 45 then (1 / 3) else 3)) else (if i.val < 48 then (1 / 3) else (if i.val < 49 then
    (1 / 9) else 0)))))) else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if
    i.val < 53 then (if i.val < 51 then (1 / 2) else 0) else (if i.val < 54 then 0 else (if
    i.val < 55 then (1 / 9) else (-1 / 3)))) else (if i.val < 59 then (if i.val < 57 then 0 else
    (if i.val < 58 then (5 / 18) else 0)) else (if i.val < 60 then (5 / 18) else 0))) else (if
    i.val < 68 then (if i.val < 65 then (if i.val < 63 then 0 else (if i.val < 64 then 0 else (5
    / 18))) else (if i.val < 66 then 0 else (if i.val < 67 then (5 / 18) else 0))) else (if
    i.val < 71 then 0 else (if i.val < 73 then (if i.val < 72 then (-5 / 3) else (-1 / 3)) else
    (if i.val < 74 then (-1 / 3) else 0))))) else (if i.val < 88 then (if i.val < 81 then (if
    i.val < 78 then (if i.val < 76 then (1 / 2) else (if i.val < 77 then 0 else (1 / 9))) else
    (if i.val < 79 then 0 else (if i.val < 80 then (-1 / 3) else (1 / 9)))) else (if i.val < 84
    then (if i.val < 82 then 0 else (if i.val < 83 then (1 / 2) else 0)) else (if i.val < 86
    then (if i.val < 85 then (1 / 9) else 0) else (if i.val < 87 then (-1 / 3) else (1 / 9)))))
    else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then 0 else (-1 / 9)) else (if
    i.val < 92 then (-1 / 9) else (if i.val < 93 then 0 else (5 / 18)))) else (if i.val < 97
    then (if i.val < 95 then 0 else (if i.val < 96 then (5 / 18) else 0)) else (if i.val < 99
    then (if i.val < 98 then 0 else (-1 / 3)) else (if i.val < 100 then (-5 / 3) else (-1 /
    3)))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val <
    107 then (if i.val < 104 then (if i.val < 102 then 0 else (if i.val < 103 then (-1 / 3) else
    (-5 / 3))) else (if i.val < 105 then (-1 / 3) else 0)) else 0) else (if i.val < 119 then 0
    else (if i.val < 122 then (if i.val < 120 then 0 else (if i.val < 121 then 0 else (1 / 15)))
    else (if i.val < 124 then (if i.val < 123 then (-1 / 5) else 0) else 0)))) else (if i.val <
    139 then (if i.val < 132 then (if i.val < 129 then (if i.val < 127 then 0 else (if i.val <
    128 then (-1 / 10) else (3 / 10))) else (if i.val < 130 then 0 else (if i.val < 131 then (3
    / 10) else 0))) else (if i.val < 135 then (if i.val < 133 then (-1 / 10) else 0) else (if
    i.val < 137 then (if i.val < 136 then (-1 / 5) else 0) else (if i.val < 138 then 0 else (1 /
    15))))) else (if i.val < 145 then 0 else (if i.val < 148 then (if i.val < 146 then 0 else
    (if i.val < 147 then 0 else (1 / 6))) else (if i.val < 150 then (if i.val < 149 then 0 else
    (-1 / 6)) else (if i.val < 151 then 0 else (-1 / 6))))))) else (if i.val < 177 then (if
    i.val < 164 then (if i.val < 158 then (if i.val < 155 then (if i.val < 153 then 0 else (if
    i.val < 154 then (1 / 6) else 0)) else 0) else (if i.val < 161 then 0 else (if i.val < 162
    then 0 else (if i.val < 163 then (1 / 6) else 0)))) else (if i.val < 170 then (if i.val <
    167 then (if i.val < 165 then (-1 / 6) else (if i.val < 166 then 0 else (-1 / 6))) else (if
    i.val < 168 then 0 else (if i.val < 169 then (1 / 6) else 0))) else (if i.val < 173 then (if
    i.val < 171 then -1 else (-1 / 5)) else (if i.val < 175 then (if i.val < 174 then (1 / 15)
    else 0) else (if i.val < 176 then 0 else (-1 / 5)))))) else (if i.val < 190 then (if i.val <
    183 then (if i.val < 180 then (if i.val < 178 then (-1 / 5) else 0) else (if i.val < 181
    then (2 / 5) else (if i.val < 182 then 0 else (-1 / 5)))) else (if i.val < 186 then (if
    i.val < 184 then (1 / 15) else 0) else (if i.val < 188 then 0 else (if i.val < 189 then (3 /
    10) else (-1 / 10))))) else (if i.val < 196 then (if i.val < 193 then (if i.val < 191 then 0
    else (if i.val < 192 then (1 / 15) else 0)) else (if i.val < 194 then (-1 / 5) else 0)) else
    (if i.val < 199 then (if i.val < 197 then (-1 / 10) else 0) else (if i.val < 201 then (if
    i.val < 200 then (3 / 10) else 0) else (if i.val < 202 then (-1 / 5) else (1 / 15)))))))))
    else (if i.val < 305 then (if i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if
    i.val < 209 then (if i.val < 206 then 0 else (if i.val < 207 then 0 else (if i.val < 208
    then (3 / 10) else (-1 / 10)))) else (if i.val < 212 then (if i.val < 210 then 0 else (if
    i.val < 211 then (1 / 15) else 0)) else (if i.val < 213 then (-1 / 5) else 0))) else (if
    i.val < 221 then (if i.val < 218 then (if i.val < 216 then (-1 / 10) else 0) else (if i.val
    < 219 then (3 / 10) else (if i.val < 220 then 0 else (-1 / 15)))) else (if i.val < 224 then
    (if i.val < 222 then (-1 / 15) else (if i.val < 223 then (-1 / 15) else (-3 / 5))) else (if
    i.val < 226 then 0 else (1 / 10))))) else (if i.val < 241 then (if i.val < 234 then (if
    i.val < 231 then (if i.val < 229 then (1 / 10) else 0) else (if i.val < 232 then (9 / 10)
    else 0)) else (if i.val < 237 then 0 else (if i.val < 239 then 0 else (if i.val < 240 then 0
    else (1 / 6))))) else (if i.val < 247 then (if i.val < 244 then (if i.val < 242 then 0 else
    (if i.val < 243 then (-1 / 6) else 0)) else (if i.val < 245 then (-1 / 6) else (if i.val <
    246 then 0 else (1 / 6)))) else (if i.val < 250 then (if i.val < 248 then 0 else (if i.val <
    249 then (-1 / 5) else -1)) else (if i.val < 252 then (if i.val < 251 then (-1 / 5) else (1
    / 15)) else 0))))) else (if i.val < 279 then (if i.val < 266 then (if i.val < 260 then (if
    i.val < 257 then (if i.val < 255 then (-1 / 5) else (if i.val < 256 then (-1 / 5) else 0))
    else (if i.val < 258 then 0 else (if i.val < 259 then (2 / 5) else 0))) else (if i.val < 263
    then (if i.val < 261 then (-1 / 5) else (if i.val < 262 then -1 else (-1 / 5))) else (if
    i.val < 264 then (1 / 15) else 0))) else (if i.val < 272 then (if i.val < 269 then (if i.val
    < 267 then (-1 / 5) else (if i.val < 268 then (-1 / 5) else 0)) else (if i.val < 270 then 0
    else (if i.val < 271 then (2 / 5) else 0))) else (if i.val < 275 then (if i.val < 273 then
    (-1 / 5) else (if i.val < 274 then (-9 / 5) else (-1 / 5))) else (if i.val < 277 then (if
    i.val < 276 then (-1 / 5) else (4 / 5)) else (if i.val < 278 then (4 / 5) else (-1 /
    15)))))) else (if i.val < 292 then (if i.val < 285 then (if i.val < 282 then (if i.val < 280
    then (-1 / 15) else (if i.val < 281 then (1 / 3) else (3 / 5))) else (2 / 15)) else (if
    i.val < 288 then (if i.val < 286 then (-4 / 15) else (2 / 15)) else (if i.val < 290 then (if
    i.val < 289 then (-4 / 15) else (2 / 15)) else (if i.val < 291 then (2 / 15) else (-1 /
    5))))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then (1 / 15) else (if
    i.val < 294 then (1 / 15) else (-1 / 5))) else (if i.val < 296 then (4 / 5) else (-1 / 15)))
    else (if i.val < 301 then (if i.val < 299 then (3 / 5) else (if i.val < 300 then (1 / 3)
    else (-1 / 15))) else (if i.val < 303 then (if i.val < 302 then (-1 / 15) else (3 / 5)) else
    (if i.val < 304 then (1 / 3) else (-1 / 15)))))))) else (if i.val < 356 then (if i.val < 330
    then (if i.val < 317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then (-1
    / 15) else (if i.val < 307 then (-1 / 15) else (-3 / 5))) else (if i.val < 309 then (-4 /
    15) else (2 / 15))) else (if i.val < 314 then (if i.val < 312 then (1 / 15) else (if i.val <
    313 then (-1 / 5) else (1 / 15))) else (if i.val < 315 then (-1 / 5) else (if i.val < 316
    then (1 / 15) else (-1 / 5))))) else (if i.val < 323 then (if i.val < 320 then (if i.val <
    318 then (1 / 15) else (if i.val < 319 then (-1 / 5) else (1 / 30))) else (if i.val < 321
    then (3 / 10) else (1 / 30))) else (if i.val < 326 then (if i.val < 324 then (-1 / 3) else
    (if i.val < 325 then (1 / 3) else (-1 / 5))) else (if i.val < 328 then (if i.val < 327 then
    (-8 / 15) else (2 / 15)) else (if i.val < 329 then (2 / 15) else (-1 / 5)))))) else (if
    i.val < 343 then (if i.val < 336 then (if i.val < 333 then (if i.val < 331 then -1 else (if
    i.val < 332 then (1 / 15) else (-1 / 5))) else (if i.val < 334 then (-1 / 3) else (if i.val
    < 335 then (-1 / 5) else (1 / 3)))) else (if i.val < 339 then (if i.val < 337 then (-1 / 3)
    else (-1 / 15)) else (if i.val < 341 then (if i.val < 340 then (-7 / 5) else (-1 / 5)) else
    (if i.val < 342 then (1 / 15) else -1)))) else (if i.val < 349 then (if i.val < 346 then (if
    i.val < 344 then (-1 / 5) else (if i.val < 345 then (-1 / 3) else (1 / 3))) else (if i.val <
    347 then (-1 / 5) else (if i.val < 348 then (-8 / 15) else (2 / 15)))) else (if i.val < 352
    then (if i.val < 350 then (2 / 15) else (if i.val < 351 then (-1 / 5) else -1)) else (if
    i.val < 354 then (if i.val < 353 then (1 / 15) else (-1 / 5)) else (if i.val < 355 then (-1
    / 3) else (-1 / 5))))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then
    (if i.val < 359 then (if i.val < 357 then (1 / 3) else (if i.val < 358 then (-1 / 3) else
    (-1 / 15))) else (if i.val < 360 then (-1 / 15) else (if i.val < 361 then (-7 / 5) else (2 /
    15)))) else (if i.val < 365 then (if i.val < 363 then (2 / 15) else (if i.val < 364 then (-8
    / 15) else (-6 / 5))) else (if i.val < 366 then (-6 / 5) else (if i.val < 367 then (-6 / 5)
    else (-7 / 5))))) else (if i.val < 374 then (if i.val < 371 then (if i.val < 369 then (-1 /
    15) else (if i.val < 370 then (-1 / 15) else (-1 / 3))) else (if i.val < 372 then (-1 / 5)
    else (if i.val < 373 then (1 / 3) else (-1 / 3)))) else (if i.val < 377 then (if i.val < 375
    then (-1 / 5) else (if i.val < 376 then (1 / 3) else (-1 / 3))) else 0))) else 0)))) else
    (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then 0 else (if i.val < 483 then 0
    else (if i.val < 496 then 0 else (if i.val < 502 then (if i.val < 499 then 0 else (if i.val
    < 500 then 0 else (if i.val < 501 then (1 / 360) else (-1 / 120)))) else 0)))) else (if
    i.val < 560 then (if i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val <
    512 then (if i.val < 510 then 0 else (if i.val < 511 then (-1 / 24) else (-1 / 120))) else
    (if i.val < 513 then (-1 / 120) else (if i.val < 514 then (1 / 360) else 0))) else (if i.val
    < 518 then (if i.val < 516 then 0 else (if i.val < 517 then (-1 / 120) else (1 / 360))) else
    (if i.val < 519 then 0 else (if i.val < 520 then 0 else (-1 / 120))))) else (if i.val < 527
    then (if i.val < 524 then (if i.val < 522 then (1 / 360) else 0) else (-1 / 360)) else (if
    i.val < 530 then (if i.val < 528 then (-1 / 40) else 0) else (if i.val < 532 then 0 else (if
    i.val < 533 then 0 else (-1 / 120)))))) else (if i.val < 547 then (if i.val < 540 then (if
    i.val < 537 then (if i.val < 535 then (-1 / 24) else (if i.val < 536 then (-1 / 120) else (1
    / 360))) else (if i.val < 538 then 0 else (if i.val < 539 then 0 else (-1 / 120)))) else (if
    i.val < 543 then (if i.val < 541 then (-1 / 24) else (if i.val < 542 then (-1 / 120) else (1
    / 360))) else (if i.val < 545 then (if i.val < 544 then 0 else (-1 / 120)) else (if i.val <
    546 then (-3 / 40) else (-1 / 120))))) else (if i.val < 553 then (if i.val < 550 then (if
    i.val < 548 then (-1 / 120) else (1 / 30)) else (if i.val < 551 then (-1 / 60) else (if
    i.val < 552 then (-1 / 60) else (1 / 36)))) else (if i.val < 556 then (if i.val < 554 then
    (-1 / 60) else (1 / 180)) else (if i.val < 558 then (if i.val < 557 then (1 / 180) else (-1
    / 12)) else (if i.val < 559 then (-7 / 180) else (1 / 180))))))) else (if i.val < 585 then
    (if i.val < 572 then (if i.val < 566 then (if i.val < 563 then (if i.val < 561 then (1 /
    180) else (if i.val < 562 then (-1 / 12) else (-7 / 180))) else (if i.val < 564 then (1 /
    180) else (if i.val < 565 then (1 / 180) else (-1 / 20)))) else (if i.val < 569 then (if
    i.val < 567 then (1 / 60) else (if i.val < 568 then (1 / 60) else (-1 / 20))) else (if i.val
    < 570 then (1 / 30) else (-1 / 60)))) else (if i.val < 578 then (if i.val < 575 then (if
    i.val < 573 then (-1 / 60) else (if i.val < 574 then (1 / 36) else (-1 / 60))) else (if
    i.val < 576 then (-1 / 60) else (if i.val < 577 then (-1 / 60) else (1 / 36)))) else (if
    i.val < 581 then (-1 / 60) else (if i.val < 583 then (if i.val < 582 then (-3 / 20) else (-7
    / 180)) else (if i.val < 584 then (-1 / 12) else (1 / 180)))))) else (if i.val < 598 then
    (if i.val < 591 then (if i.val < 588 then (if i.val < 586 then (1 / 180) else (if i.val <
    587 then (1 / 60) else (-1 / 20))) else (if i.val < 589 then (1 / 60) else (if i.val < 590
    then (-1 / 20) else (1 / 60)))) else (if i.val < 594 then (if i.val < 592 then (-1 / 20)
    else (if i.val < 593 then (1 / 60) else (-1 / 20))) else (if i.val < 596 then (if i.val <
    595 then (1 / 60) else (3 / 20)) else (1 / 60)))) else (if i.val < 604 then (if i.val < 601
    then (if i.val < 599 then (-1 / 720) else (if i.val < 600 then (-1 / 80) else (-1 / 720)))
    else (if i.val < 602 then (-1 / 720) else (if i.val < 603 then (7 / 720) else (-1 / 720))))
    else (if i.val < 607 then (if i.val < 605 then (1 / 48) else (if i.val < 606 then (-1 / 720)
    else (7 / 720))) else (if i.val < 609 then (if i.val < 608 then (-1 / 720) else (1 / 48))
    else (if i.val < 610 then (-1 / 720) else (-1 / 240))))))))) else (if i.val < 713 then (if
    i.val < 662 then (if i.val < 636 then (if i.val < 623 then (if i.val < 617 then (if i.val <
    614 then (if i.val < 612 then (-1 / 240) else (1 / 80)) else (if i.val < 615 then (3 / 80)
    else (1 / 240))) else (if i.val < 620 then (if i.val < 618 then (1 / 240) else (-1 / 80))
    else (if i.val < 621 then (1 / 240) else (if i.val < 622 then (1 / 240) else (-1 / 80)))))
    else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then (-1 / 80) else (1 /
    240)) else (if i.val < 627 then (-1 / 48) else (1 / 720))) else (if i.val < 632 then (if
    i.val < 630 then (-7 / 720) else (if i.val < 631 then (7 / 720) else (1 / 48))) else (if
    i.val < 634 then (-1 / 720) else (-1 / 240))))) else (if i.val < 649 then (if i.val < 642
    then (if i.val < 639 then (if i.val < 637 then (1 / 80) else (if i.val < 638 then (1 / 80)
    else (-1 / 240))) else (if i.val < 640 then (-1 / 240) else (1 / 80))) else (if i.val < 645
    then (-1 / 240) else (if i.val < 647 then (if i.val < 646 then (-3 / 80) else (-1 / 80))
    else (if i.val < 648 then (-1 / 80) else (1 / 240))))) else (if i.val < 655 then (if i.val <
    652 then (if i.val < 650 then (1 / 240) else (if i.val < 651 then (1 / 720) else (-1 / 48)))
    else (if i.val < 653 then (1 / 720) else (if i.val < 654 then (-7 / 720) else (1 / 720))))
    else (if i.val < 658 then (if i.val < 656 then (-1 / 48) else (if i.val < 657 then (1 / 720)
    else (-7 / 720))) else (if i.val < 660 then (if i.val < 659 then (1 / 720) else (1 / 80))
    else (1 / 720)))))) else 0) else 0)))

/-- Incoming exact raw coordinates; validity is checked separately. -/
def fullClaim : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if
    i.val < 51 then 0 else (if i.val < 52 then (1 / 3) else -1)) else 0) else (if i.val < 59
    then (if i.val < 57 then (1 / 3) else (if i.val < 58 then (1 / 2) else 0)) else (if i.val <
    60 then (1 / 2) else 0))) else (if i.val < 68 then (if i.val < 65 then (if i.val < 63 then
    -1 else (if i.val < 64 then (2 / 3) else (1 / 2))) else (if i.val < 66 then 0 else (if i.val
    < 67 then (1 / 2) else 0))) else (if i.val < 71 then (if i.val < 69 then 0 else (if i.val <
    70 then -1 else (2 / 3))) else (if i.val < 73 then 0 else (if i.val < 74 then 0 else (-4 /
    3)))))) else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then
    0 else (if i.val < 77 then (1 / 3) else 0)) else 0) else (if i.val < 84 then (if i.val < 82
    then (1 / 3) else (if i.val < 83 then 0 else (1 / 3))) else 0)) else (if i.val < 94 then (if
    i.val < 91 then (if i.val < 89 then (1 / 3) else 0) else (if i.val < 92 then 0 else (if
    i.val < 93 then 0 else (1 / 2)))) else (if i.val < 97 then (if i.val < 95 then 0 else (if
    i.val < 96 then (1 / 2) else 0)) else (if i.val < 99 then (if i.val < 98 then (2 / 3) else
    0) else 0)))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if
    i.val < 107 then (if i.val < 104 then (if i.val < 102 then (-4 / 3) else 0) else (if i.val <
    105 then 0 else (if i.val < 106 then (-4 / 3) else 0))) else (if i.val < 110 then (if i.val
    < 108 then 0 else (if i.val < 109 then 0 else (-1 / 2))) else (if i.val < 111 then (-1 / 2)
    else (if i.val < 112 then 0 else (-1 / 2))))) else (if i.val < 119 then (if i.val < 116 then
    (if i.val < 114 then (-1 / 2) else 0) else 0) else (if i.val < 122 then (if i.val < 120 then
    (-1 / 2) else (if i.val < 121 then (-1 / 2) else (1 / 15))) else (if i.val < 124 then (if
    i.val < 123 then (4259 / 3510) else (161 / 270)) else (if i.val < 125 then (-745 / 351) else
    (407 / 540)))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129 then (if
    i.val < 127 then (12553 / 23868) else (if i.val < 128 then (-193 / 1080) else (27371 /
    14040))) else (if i.val < 130 then (-991 / 1404) else (if i.val < 131 then (791 / 390) else
    (-2797 / 3978)))) else (if i.val < 135 then (if i.val < 133 then (-23 / 1080) else (if i.val
    < 134 then (899 / 1080) else (701 / 1326))) else (if i.val < 137 then (if i.val < 136 then
    (6047 / 4680) else (559 / 1080)) else (if i.val < 138 then (-745 / 351) else (1 / 15)))))
    else (if i.val < 145 then (if i.val < 142 then (if i.val < 140 then (3853 / 1989) else (3527
    / 5265)) else (if i.val < 143 then (-1490 / 1053) else (if i.val < 144 then (7706 / 5967)
    else (3527 / 5265)))) else (if i.val < 148 then (if i.val < 146 then (3527 / 5265) else (if
    i.val < 147 then (-1490 / 1053) else (20933 / 21060))) else (if i.val < 150 then (if i.val <
    149 then (-4229 / 71604) else (13913 / 21060)) else (if i.val < 151 then (-4229 / 71604)
    else (13913 / 21060))))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158
    then (if i.val < 155 then (if i.val < 153 then (-4229 / 71604) else (if i.val < 154 then
    (20933 / 21060) else (-4229 / 71604))) else (if i.val < 156 then (3527 / 5265) else (if
    i.val < 157 then (3527 / 5265) else (-1490 / 1053)))) else (if i.val < 161 then (if i.val <
    159 then (7706 / 5967) else (3527 / 5265)) else (if i.val < 162 then (-1490 / 1053) else (if
    i.val < 163 then (20933 / 21060) else (-4229 / 71604))))) else (if i.val < 170 then (if
    i.val < 167 then (if i.val < 165 then (13913 / 21060) else (if i.val < 166 then (-4229 /
    71604) else (13913 / 21060))) else (if i.val < 168 then (-4229 / 71604) else (if i.val < 169
    then (20933 / 21060) else (-4229 / 71604)))) else (if i.val < 173 then (if i.val < 171 then
    -1 else (-1 / 5)) else (if i.val < 175 then (if i.val < 174 then (1481 / 1053) else (161 /
    135)) else (if i.val < 176 then (-3050 / 1053) else (-1 / 5)))))) else (if i.val < 190 then
    (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then (-1 / 5) else (if i.val < 179
    then (407 / 270) else (-2203 / 11934))) else (if i.val < 181 then (4327 / 2106) else (if
    i.val < 182 then (-133 / 2106) else (4259 / 3510)))) else (if i.val < 186 then (if i.val <
    184 then (1 / 15) else (if i.val < 185 then (161 / 270) else (-745 / 351))) else (if i.val <
    188 then (if i.val < 187 then (407 / 540) else (12553 / 23868)) else (if i.val < 189 then
    (27371 / 14040) else (-193 / 1080))))) else (if i.val < 196 then (if i.val < 193 then (if
    i.val < 191 then (-991 / 1404) else (if i.val < 192 then (1 / 15) else (3853 / 1989))) else
    (if i.val < 194 then (6047 / 4680) else (if i.val < 195 then (559 / 1080) else (-745 /
    351)))) else (if i.val < 199 then (if i.val < 197 then (-23 / 1080) else (if i.val < 198
    then (899 / 1080) else (701 / 1326))) else (if i.val < 201 then (if i.val < 200 then (791 /
    390) else (-2797 / 3978)) else (if i.val < 202 then (4259 / 3510) else (1 / 15))))))))) else
    (if i.val < 305 then (if i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if
    i.val < 209 then (if i.val < 206 then (if i.val < 204 then (161 / 270) else (if i.val < 205
    then (-745 / 351) else (407 / 540))) else (if i.val < 207 then (12553 / 23868) else (if
    i.val < 208 then (27371 / 14040) else (-193 / 1080)))) else (if i.val < 212 then (if i.val <
    210 then (-991 / 1404) else (if i.val < 211 then (1 / 15) else (3853 / 1989))) else (if
    i.val < 213 then (6047 / 4680) else (if i.val < 214 then (559 / 1080) else (-745 / 351)))))
    else (if i.val < 221 then (if i.val < 218 then (if i.val < 216 then (-23 / 1080) else (if
    i.val < 217 then (899 / 1080) else (701 / 1326))) else (if i.val < 219 then (791 / 390) else
    (if i.val < 220 then (-2797 / 3978) else (-1 / 15)))) else (if i.val < 224 then (if i.val <
    222 then (-1 / 15) else (if i.val < 223 then (-1 / 15) else (1285 / 468))) else (if i.val <
    226 then (if i.val < 225 then (161 / 60) else (-745 / 117)) else (1 / 10))))) else (if i.val
    < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then (1 / 10) else (if
    i.val < 230 then (407 / 120) else (-953 / 1768))) else (if i.val < 232 then (4637 / 936)
    else (if i.val < 233 then (7 / 936) else (3527 / 5265)))) else (if i.val < 237 then (if
    i.val < 235 then (3527 / 5265) else (if i.val < 236 then (-1490 / 1053) else (7706 / 5967)))
    else (if i.val < 239 then (3527 / 5265) else (if i.val < 240 then (-1490 / 1053) else (20933
    / 21060))))) else (if i.val < 247 then (if i.val < 244 then (if i.val < 242 then (-4229 /
    71604) else (if i.val < 243 then (13913 / 21060) else (-4229 / 71604))) else (if i.val < 245
    then (13913 / 21060) else (if i.val < 246 then (-4229 / 71604) else (20933 / 21060)))) else
    (if i.val < 250 then (if i.val < 248 then (-4229 / 71604) else (if i.val < 249 then (-1 / 5)
    else -1)) else (if i.val < 252 then (if i.val < 251 then (-1 / 5) else (1481 / 1053)) else
    (if i.val < 253 then (161 / 135) else (-3050 / 1053))))))) else (if i.val < 279 then (if
    i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then (-1 / 5)
    else (if i.val < 256 then (-1 / 5) else (407 / 270))) else (if i.val < 258 then (-2203 /
    11934) else (if i.val < 259 then (4327 / 2106) else (-133 / 2106)))) else (if i.val < 263
    then (if i.val < 261 then (-1 / 5) else (if i.val < 262 then -1 else (-1 / 5))) else (if
    i.val < 264 then (1481 / 1053) else (if i.val < 265 then (161 / 135) else (-3050 / 1053)))))
    else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then (-1 / 5) else (if i.val
    < 268 then (-1 / 5) else (407 / 270))) else (if i.val < 270 then (-2203 / 11934) else (if
    i.val < 271 then (4327 / 2106) else (-133 / 2106)))) else (if i.val < 275 then (if i.val <
    273 then (-1 / 5) else (if i.val < 274 then (-9 / 5) else (-1 / 5))) else (if i.val < 277
    then (if i.val < 276 then (-1 / 5) else (4 / 5)) else (if i.val < 278 then (4 / 5) else (-1
    / 15)))))) else (if i.val < 292 then (if i.val < 285 then (if i.val < 282 then (if i.val <
    280 then (-1 / 15) else (if i.val < 281 then (1 / 3) else (3 / 5))) else (2 / 15)) else (if
    i.val < 288 then (if i.val < 286 then (-4 / 15) else (2 / 15)) else (if i.val < 290 then (if
    i.val < 289 then (-4 / 15) else (2 / 15)) else (if i.val < 291 then (2 / 15) else (-1 /
    5))))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then (1 / 15) else (if
    i.val < 294 then (1 / 15) else (-1 / 5))) else (if i.val < 296 then (4 / 5) else (-1 / 15)))
    else (if i.val < 301 then (if i.val < 299 then (3 / 5) else (if i.val < 300 then (1 / 3)
    else (-1 / 15))) else (if i.val < 303 then (if i.val < 302 then (-1 / 15) else (3 / 5)) else
    (if i.val < 304 then (1 / 3) else (-1 / 15)))))))) else (if i.val < 356 then (if i.val < 330
    then (if i.val < 317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then (-1
    / 15) else (if i.val < 307 then (-1 / 15) else (-3 / 5))) else (if i.val < 309 then (-4 /
    15) else (2 / 15))) else (if i.val < 314 then (if i.val < 312 then (1 / 15) else (if i.val <
    313 then (-1 / 5) else (1 / 15))) else (if i.val < 315 then (-1 / 5) else (if i.val < 316
    then (1 / 15) else (-1 / 5))))) else (if i.val < 323 then (if i.val < 320 then (if i.val <
    318 then (1 / 15) else (if i.val < 319 then (-1 / 5) else (1 / 30))) else (if i.val < 321
    then (3 / 10) else (1 / 30))) else (if i.val < 326 then (if i.val < 324 then (-1 / 3) else
    (if i.val < 325 then (1 / 3) else (-1 / 5))) else (if i.val < 328 then (if i.val < 327 then
    (-8 / 15) else (2 / 15)) else (if i.val < 329 then (2 / 15) else (-1 / 5)))))) else (if
    i.val < 343 then (if i.val < 336 then (if i.val < 333 then (if i.val < 331 then -1 else (if
    i.val < 332 then (1 / 15) else (-1 / 5))) else (if i.val < 334 then (-1 / 3) else (if i.val
    < 335 then (-1 / 5) else (1 / 3)))) else (if i.val < 339 then (if i.val < 337 then (-1 / 3)
    else (-1 / 15)) else (if i.val < 341 then (if i.val < 340 then (-7 / 5) else (-1 / 5)) else
    (if i.val < 342 then (1 / 15) else -1)))) else (if i.val < 349 then (if i.val < 346 then (if
    i.val < 344 then (-1 / 5) else (if i.val < 345 then (-1 / 3) else (1 / 3))) else (if i.val <
    347 then (-1 / 5) else (if i.val < 348 then (-8 / 15) else (2 / 15)))) else (if i.val < 352
    then (if i.val < 350 then (2 / 15) else (if i.val < 351 then (-1 / 5) else -1)) else (if
    i.val < 354 then (if i.val < 353 then (1 / 15) else (-1 / 5)) else (if i.val < 355 then (-1
    / 3) else (-1 / 5))))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then
    (if i.val < 359 then (if i.val < 357 then (1 / 3) else (if i.val < 358 then (-1 / 3) else
    (-1 / 15))) else (if i.val < 360 then (-1 / 15) else (if i.val < 361 then (-7 / 5) else (2 /
    15)))) else (if i.val < 365 then (if i.val < 363 then (2 / 15) else (if i.val < 364 then (-8
    / 15) else (-6 / 5))) else (if i.val < 366 then (-6 / 5) else (if i.val < 367 then (-6 / 5)
    else (-7 / 5))))) else (if i.val < 374 then (if i.val < 371 then (if i.val < 369 then (-1 /
    15) else (if i.val < 370 then (-1 / 15) else (-1 / 3))) else (if i.val < 372 then (-1 / 5)
    else (if i.val < 373 then (1 / 3) else (-1 / 3)))) else (if i.val < 377 then (if i.val < 375
    then (-1 / 5) else (if i.val < 376 then (1 / 3) else (-1 / 3))) else (if i.val < 379 then
    (-565 / 351) else (if i.val < 380 then (-197 / 270) else (-47 / 45)))))) else (if i.val <
    394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then (-24779 / 10530)
    else (if i.val < 383 then (-52873 / 21060) else (-565 / 351))) else (if i.val < 385 then
    (-3527 / 5265) else (if i.val < 386 then (-17423 / 21060) else (-3527 / 5265)))) else (if
    i.val < 390 then (if i.val < 388 then (-17423 / 21060) else (if i.val < 389 then (-24779 /
    10530) else (-52873 / 21060))) else (if i.val < 392 then (if i.val < 391 then (-1130 / 1053)
    else (-3527 / 5265)) else (if i.val < 393 then (-17423 / 21060) else (-3527 / 5265))))) else
    (if i.val < 400 then (if i.val < 397 then (if i.val < 395 then (-17423 / 21060) else (if
    i.val < 396 then (-24779 / 10530) else (-52873 / 21060))) else (if i.val < 398 then (-1130 /
    1053) else (if i.val < 399 then (-2105 / 1053) else (-197 / 270)))) else (if i.val < 403
    then (if i.val < 401 then (-47 / 45) else (-565 / 351)) else (if i.val < 405 then (if i.val
    < 404 then (-565 / 351) else (-197 / 270)) else (if i.val < 406 then (-47 / 45) else (-565 /
    351)))))))))) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val
    < 432 then (if i.val < 419 then (if i.val < 413 then (if i.val < 410 then (if i.val < 408
    then (-565 / 351) else (if i.val < 409 then (-565 / 351) else (-565 / 117))) else (if i.val
    < 411 then (-3527 / 5265) else (if i.val < 412 then (-17423 / 21060) else (-3527 / 5265))))
    else (if i.val < 416 then (if i.val < 414 then (-17423 / 21060) else (if i.val < 415 then
    (-1130 / 1053) else (-2105 / 1053))) else (if i.val < 417 then (-2105 / 1053) else (if i.val
    < 418 then (-1199 / 59670) else (-8909 / 59670))))) else (if i.val < 425 then (if i.val <
    422 then (if i.val < 420 then (-73 / 195) else (if i.val < 421 then (1106 / 5967) else (-809
    / 59670))) else (if i.val < 423 then (-547 / 3510) else (if i.val < 424 then (-73 / 390)
    else (-343 / 2340)))) else (if i.val < 428 then (if i.val < 426 then (4229 / 23868) else (if
    i.val < 427 then (-2723 / 119340) else (2212 / 17901))) else (-5054 / 89505)))) else (if
    i.val < 445 then (if i.val < 438 then (if i.val < 435 then (if i.val < 433 then (-146 / 585)
    else (if i.val < 434 then (-73 / 585) else (-5054 / 89505))) else (if i.val < 436 then
    (-5054 / 89505) else (if i.val < 437 then (4229 / 35802) else (2212 / 17901)))) else (if
    i.val < 441 then (-5054 / 89505) else (if i.val < 443 then (if i.val < 442 then (-5054 /
    89505) else (-146 / 585)) else (if i.val < 444 then (-73 / 585) else (-5054 / 89505)))))
    else (if i.val < 451 then (if i.val < 448 then (if i.val < 446 then (-5054 / 89505) else (if
    i.val < 447 then (4229 / 35802) else (-13627 / 89505))) else (if i.val < 449 then (-178 /
    1755) else (if i.val < 450 then (-7 / 26) else (-1199 / 59670)))) else (if i.val < 454 then
    (if i.val < 452 then (1106 / 5967) else (if i.val < 453 then (-809 / 59670) else (-8909 /
    59670))) else (if i.val < 456 then (if i.val < 455 then (-73 / 195) else (-547 / 3510)) else
    (if i.val < 457 then (-73 / 390) else (4229 / 23868))))))) else (if i.val < 483 then (if
    i.val < 470 then (if i.val < 464 then (if i.val < 461 then (if i.val < 459 then (-343 /
    2340) else (if i.val < 460 then (-2723 / 119340) else (-1199 / 59670))) else (if i.val < 462
    then (1106 / 5967) else (if i.val < 463 then (-809 / 59670) else (-8909 / 59670)))) else (if
    i.val < 467 then (if i.val < 465 then (-73 / 195) else (if i.val < 466 then (-547 / 3510)
    else (-73 / 390))) else (if i.val < 468 then (4229 / 23868) else (if i.val < 469 then (-343
    / 2340) else (-2723 / 119340))))) else (if i.val < 476 then (if i.val < 473 then (if i.val <
    471 then (-14657 / 39780) else (if i.val < 472 then (-109 / 780) else (-73 / 130))) else (if
    i.val < 474 then (2212 / 17901) else (-5054 / 89505))) else (if i.val < 479 then (if i.val <
    477 then (-5054 / 89505) else (if i.val < 478 then (-5054 / 89505) else (-146 / 585))) else
    (if i.val < 481 then (if i.val < 480 then (-73 / 585) else (-5054 / 89505)) else (if i.val <
    482 then (-5054 / 89505) else (4229 / 35802)))))) else (if i.val < 496 then (if i.val < 489
    then (if i.val < 486 then (if i.val < 484 then (-13627 / 89505) else (if i.val < 485 then
    (-178 / 1755) else (-7 / 26))) else (if i.val < 487 then (-13627 / 89505) else (if i.val <
    488 then (-178 / 1755) else (-7 / 26)))) else (if i.val < 492 then (if i.val < 490 then
    (3853 / 1989) else (7706 / 5967)) else (if i.val < 494 then (if i.val < 493 then (15740 /
    5967) else (3853 / 1989)) else (if i.val < 495 then (3853 / 1989) else (3853 / 663))))) else
    (if i.val < 502 then (if i.val < 499 then (if i.val < 497 then (7706 / 5967) else (15740 /
    5967)) else (if i.val < 500 then (-539 / 5616) else (if i.val < 501 then (1 / 360) else (101
    / 1560)))) else (if i.val < 505 then (if i.val < 503 then (67 / 2160) else (if i.val < 504
    then (-539 / 8424) else (2923 / 84240))) else (if i.val < 507 then (if i.val < 506 then
    (2923 / 84240) else (-539 / 8424)) else (2923 / 84240))))))) else (if i.val < 560 then (if
    i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val <
    510 then (-1085 / 8424) else (if i.val < 511 then (-1 / 24) else (-1 / 120))) else (if i.val
    < 513 then (-1 / 120) else (if i.val < 514 then (76 / 1053) else (67 / 1080)))) else (if
    i.val < 518 then (if i.val < 516 then (-539 / 5616) else (if i.val < 517 then (101 / 1560)
    else (1 / 360))) else (if i.val < 519 then (67 / 2160) else (if i.val < 520 then (-539 /
    5616) else (101 / 1560))))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
    then (1 / 360) else (if i.val < 523 then (67 / 2160) else (-539 / 1872))) else (-1 / 360))
    else (if i.val < 530 then (if i.val < 528 then (553 / 3744) else (if i.val < 529 then (67 /
    480) else (-539 / 8424))) else (if i.val < 532 then (2923 / 84240) else (if i.val < 533 then
    (-1085 / 8424) else (-1 / 120)))))) else (if i.val < 547 then (if i.val < 540 then (if i.val
    < 537 then (if i.val < 535 then (-1 / 24) else (if i.val < 536 then (-1 / 120) else (76 /
    1053))) else (if i.val < 538 then (67 / 1080) else (if i.val < 539 then (-1085 / 8424) else
    (-1 / 120)))) else (if i.val < 543 then (if i.val < 541 then (-1 / 24) else (if i.val < 542
    then (-1 / 120) else (76 / 1053))) else (if i.val < 545 then (if i.val < 544 then (67 /
    1080) else (-1 / 120)) else (if i.val < 546 then (-3 / 40) else (-1 / 120))))) else (if
    i.val < 553 then (if i.val < 550 then (if i.val < 548 then (-1 / 120) else (1 / 30)) else
    (if i.val < 551 then (-1 / 60) else (if i.val < 552 then (-1 / 60) else (1 / 36)))) else (if
    i.val < 556 then (if i.val < 554 then (-1 / 60) else (1 / 180)) else (if i.val < 558 then
    (if i.val < 557 then (1 / 180) else (-1 / 12)) else (if i.val < 559 then (-7 / 180) else (1
    / 180))))))) else (if i.val < 585 then (if i.val < 572 then (if i.val < 566 then (if i.val <
    563 then (if i.val < 561 then (1 / 180) else (if i.val < 562 then (-1 / 12) else (-7 /
    180))) else (if i.val < 564 then (1 / 180) else (if i.val < 565 then (1 / 180) else (-1 /
    20)))) else (if i.val < 569 then (if i.val < 567 then (1 / 60) else (if i.val < 568 then (1
    / 60) else (-1 / 20))) else (if i.val < 570 then (1 / 30) else (-1 / 60)))) else (if i.val <
    578 then (if i.val < 575 then (if i.val < 573 then (-1 / 60) else (if i.val < 574 then (1 /
    36) else (-1 / 60))) else (if i.val < 576 then (-1 / 60) else (if i.val < 577 then (-1 / 60)
    else (1 / 36)))) else (if i.val < 581 then (-1 / 60) else (if i.val < 583 then (if i.val <
    582 then (-3 / 20) else (-7 / 180)) else (if i.val < 584 then (-1 / 12) else (1 / 180))))))
    else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then (if i.val < 586 then (1
    / 180) else (if i.val < 587 then (1 / 60) else (-1 / 20))) else (if i.val < 589 then (1 /
    60) else (if i.val < 590 then (-1 / 20) else (1 / 60)))) else (if i.val < 594 then (if i.val
    < 592 then (-1 / 20) else (if i.val < 593 then (1 / 60) else (-1 / 20))) else (if i.val <
    596 then (if i.val < 595 then (1 / 60) else (3 / 20)) else (1 / 60)))) else (if i.val < 604
    then (if i.val < 601 then (if i.val < 599 then (-1 / 720) else (if i.val < 600 then (-1 /
    80) else (-1 / 720))) else (if i.val < 602 then (-1 / 720) else (if i.val < 603 then (7 /
    720) else (-1 / 720)))) else (if i.val < 607 then (if i.val < 605 then (1 / 48) else (if
    i.val < 606 then (-1 / 720) else (7 / 720))) else (if i.val < 609 then (if i.val < 608 then
    (-1 / 720) else (1 / 48)) else (if i.val < 610 then (-1 / 720) else (-1 / 240))))))))) else
    (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val < 623 then (if
    i.val < 617 then (if i.val < 614 then (if i.val < 612 then (-1 / 240) else (1 / 80)) else
    (if i.val < 615 then (3 / 80) else (1 / 240))) else (if i.val < 620 then (if i.val < 618
    then (1 / 240) else (-1 / 80)) else (if i.val < 621 then (1 / 240) else (if i.val < 622 then
    (1 / 240) else (-1 / 80))))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624
    then (-1 / 80) else (1 / 240)) else (if i.val < 627 then (-1 / 48) else (1 / 720))) else (if
    i.val < 632 then (if i.val < 630 then (-7 / 720) else (if i.val < 631 then (7 / 720) else (1
    / 48))) else (if i.val < 634 then (-1 / 720) else (-1 / 240))))) else (if i.val < 649 then
    (if i.val < 642 then (if i.val < 639 then (if i.val < 637 then (1 / 80) else (if i.val < 638
    then (1 / 80) else (-1 / 240))) else (if i.val < 640 then (-1 / 240) else (1 / 80))) else
    (if i.val < 645 then (-1 / 240) else (if i.val < 647 then (if i.val < 646 then (-3 / 80)
    else (-1 / 80)) else (if i.val < 648 then (-1 / 80) else (1 / 240))))) else (if i.val < 655
    then (if i.val < 652 then (if i.val < 650 then (1 / 240) else (if i.val < 651 then (1 / 720)
    else (-1 / 48))) else (if i.val < 653 then (1 / 720) else (if i.val < 654 then (-7 / 720)
    else (1 / 720)))) else (if i.val < 658 then (if i.val < 656 then (-1 / 48) else (if i.val <
    657 then (1 / 720) else (-7 / 720))) else (if i.val < 660 then (if i.val < 659 then (1 /
    720) else (1 / 80)) else (1 / 720)))))) else (if i.val < 687 then (if i.val < 674 then (if
    i.val < 668 then (if i.val < 665 then (if i.val < 663 then (-491 / 5616) else (if i.val <
    664 then (-79 / 2160) else (-5299 / 42120))) else (if i.val < 666 then (-491 / 5616) else
    (if i.val < 667 then (641 / 28080) else (-629 / 28080)))) else (if i.val < 671 then (if
    i.val < 669 then (-5023 / 28080) else (if i.val < 670 then (539 / 5616) else (1421 /
    28080))) else (if i.val < 672 then (-1409 / 28080) else (if i.val < 673 then (-5023 / 28080)
    else (4637 / 238680))))) else (if i.val < 680 then (if i.val < 677 then (if i.val < 675 then
    (83 / 17680) else (if i.val < 676 then (-2077 / 238680) else (-227 / 9360))) else (if i.val
    < 678 then (4637 / 238680) else (if i.val < 679 then (2371 / 477360) else (-7 / 780)))) else
    (if i.val < 683 then (if i.val < 681 then (-227 / 9360) else (-2923 / 84240)) else (if i.val
    < 685 then (if i.val < 684 then (-5299 / 42120) else (-491 / 8424)) else (if i.val < 686
    then (539 / 8424) else (1 / 7020)))))) else (if i.val < 700 then (if i.val < 693 then (if
    i.val < 690 then (1 / 7020) else (if i.val < 691 then (-5023 / 42120) else (if i.val < 692
    then (-5023 / 42120) else (4637 / 358020)))) else (if i.val < 696 then (if i.val < 694 then
    (4637 / 358020) else (-1913 / 1432080)) else (if i.val < 698 then (-1913 / 1432080) else
    (-227 / 14040)))) else (if i.val < 706 then (if i.val < 703 then (if i.val < 701 then (-2923
    / 84240) else (if i.val < 702 then (-2923 / 84240) else (-5299 / 42120))) else (if i.val <
    704 then (-491 / 8424) else (if i.val < 705 then (539 / 8424) else (1 / 7020)))) else (if
    i.val < 709 then (1 / 7020) else (if i.val < 711 then (-5023 / 42120) else (4637 /
    358020))))))) else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val
    < 719 then (if i.val < 716 then (-1913 / 1432080) else (if i.val < 717 then (-1913 /
    1432080) else (-227 / 14040))) else (if i.val < 722 then (if i.val < 720 then (-115 / 1053)
    else (if i.val < 721 then (-737 / 42120) else (47 / 42120))) else (if i.val < 723 then
    (-2159 / 8424) else (if i.val < 724 then (7399 / 286416) else (-5203 / 1432080))))) else (if
    i.val < 731 then (if i.val < 728 then (if i.val < 726 then (-77 / 28080) else (if i.val <
    727 then (-187 / 5616) else (-79 / 2160))) else (if i.val < 729 then (-491 / 5616) else (if
    i.val < 730 then (-491 / 5616) else (641 / 28080)))) else (if i.val < 734 then (if i.val <
    732 then (539 / 5616) else (if i.val < 733 then (1421 / 28080) else (-629 / 28080))) else
    (if i.val < 736 then (if i.val < 735 then (-5023 / 28080) else (-1409 / 28080)) else (if
    i.val < 737 then (-5023 / 28080) else (4637 / 238680)))))) else (if i.val < 751 then (if
    i.val < 744 then (if i.val < 741 then (if i.val < 739 then (83 / 17680) else (if i.val < 740
    then (4637 / 238680) else (2371 / 477360))) else (if i.val < 742 then (-2077 / 238680) else
    (if i.val < 743 then (-227 / 9360) else (-7 / 780)))) else (if i.val < 747 then (if i.val <
    745 then (-227 / 9360) else (if i.val < 746 then (-79 / 2160) else (-491 / 5616))) else (if
    i.val < 749 then (if i.val < 748 then (-491 / 5616) else (641 / 28080)) else (if i.val < 750
    then (539 / 5616) else (1421 / 28080))))) else (if i.val < 757 then (if i.val < 754 then (if
    i.val < 752 then (-629 / 28080) else (if i.val < 753 then (-5023 / 28080) else (-1409 /
    28080))) else (if i.val < 755 then (-5023 / 28080) else (if i.val < 756 then (4637 / 238680)
    else (83 / 17680)))) else (if i.val < 760 then (if i.val < 758 then (4637 / 238680) else (if
    i.val < 759 then (2371 / 477360) else (-2077 / 238680))) else (if i.val < 762 then (if i.val
    < 761 then (-227 / 9360) else (-7 / 780)) else (if i.val < 763 then (-227 / 9360) else (-491
    / 1872))))))) else (if i.val < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val
    < 767 then (if i.val < 765 then (-193 / 4680) else (if i.val < 766 then (199 / 4680) else
    (-5023 / 9360))) else (if i.val < 768 then (4637 / 79560) else (if i.val < 769 then (-2551 /
    318240) else (-5 / 1248)))) else (if i.val < 773 then (if i.val < 771 then (-227 / 3120)
    else (-2923 / 84240)) else (if i.val < 774 then (-491 / 8424) else (if i.val < 775 then (539
    / 8424) else (1 / 7020))))) else (if i.val < 782 then (if i.val < 779 then (1 / 7020) else
    (if i.val < 780 then (-5023 / 42120) else (if i.val < 781 then (-5023 / 42120) else (4637 /
    358020)))) else (if i.val < 785 then (if i.val < 783 then (4637 / 358020) else (-1913 /
    1432080)) else (if i.val < 787 then (-1913 / 1432080) else (-227 / 14040))))) else (if i.val
    < 802 then (if i.val < 795 then (if i.val < 792 then (if i.val < 790 then (-115 / 1053) else
    (if i.val < 791 then (-737 / 42120) else (47 / 42120))) else (if i.val < 793 then (-2159 /
    8424) else (if i.val < 794 then (7399 / 286416) else (-5203 / 1432080)))) else (if i.val <
    798 then (if i.val < 796 then (-77 / 28080) else (if i.val < 797 then (-187 / 5616) else
    (-115 / 1053))) else (if i.val < 800 then (if i.val < 799 then (-737 / 42120) else (47 /
    42120)) else (if i.val < 801 then (-2159 / 8424) else (7399 / 286416))))) else (if i.val <
    808 then (if i.val < 805 then (if i.val < 803 then (-5203 / 1432080) else (if i.val < 804
    then (-77 / 28080) else (-187 / 5616))) else (if i.val < 806 then (-77 / 112320) else (-77 /
    168480))) else (if i.val < 811 then (if i.val < 809 then (-31 / 33696) else (-77 / 112320))
    else (if i.val < 813 then (if i.val < 812 then (-77 / 37440) else (-77 / 168480)) else (-31
    / 33696))))))))))

/-- Incoming exact raw coordinates; validity is checked separately. -/
def primitiveClaim : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then 0
    else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if
    i.val < 51 then 0 else (if i.val < 52 then (1 / 3) else -1)) else 0) else (if i.val < 59
    then (if i.val < 57 then 0 else (if i.val < 58 then (1 / 2) else 0)) else (if i.val < 60
    then (1 / 2) else 0))) else (if i.val < 68 then (if i.val < 65 then (if i.val < 63 then -1
    else (if i.val < 64 then 0 else (1 / 2))) else (if i.val < 66 then 0 else (if i.val < 67
    then (1 / 2) else 0))) else (if i.val < 71 then (if i.val < 69 then 0 else (if i.val < 70
    then -1 else 0)) else 0))) else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then
    (if i.val < 76 then 0 else (if i.val < 77 then (1 / 3) else 0)) else 0) else (if i.val < 84
    then (if i.val < 82 then 0 else (if i.val < 83 then 0 else (1 / 3))) else 0)) else (if i.val
    < 94 then (if i.val < 91 then 0 else (if i.val < 92 then 0 else (if i.val < 93 then 0 else
    (1 / 2)))) else (if i.val < 97 then (if i.val < 95 then 0 else (if i.val < 96 then (1 / 2)
    else 0)) else 0))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if
    i.val < 107 then 0 else (if i.val < 110 then (if i.val < 108 then 0 else (if i.val < 109
    then 0 else (-1 / 2))) else (if i.val < 111 then (-1 / 2) else (if i.val < 112 then 0 else
    (-1 / 2))))) else (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then (-1 / 2)
    else 0) else 0) else (if i.val < 122 then (if i.val < 120 then (-1 / 2) else (if i.val < 121
    then (-1 / 2) else 0)) else 0))) else 0) else 0)) else 0) else 0)

/-- Incoming exact raw coordinates; validity is checked separately. -/
def beforeAverageClaim : Coordinates 815 :=
  fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if
    i.val < 25 then 0 else (if i.val < 37 then 0 else (if i.val < 43 then 0 else (if i.val < 46
    then 0 else (if i.val < 48 then 0 else (if i.val < 49 then (10 / 9) else -1)))))) else (if
    i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51
    then 0 else (if i.val < 52 then (1 / 3) else -1)) else 0) else (if i.val < 59 then (if i.val
    < 57 then (-1 / 3) else (if i.val < 58 then (-1 / 18) else (1 / 2))) else (if i.val < 60
    then (-1 / 18) else (if i.val < 61 then (1 / 2) else 0)))) else (if i.val < 68 then (if
    i.val < 65 then (if i.val < 63 then -1 else (if i.val < 64 then (7 / 3) else (-1 / 18)))
    else (if i.val < 66 then (1 / 2) else (if i.val < 67 then (-1 / 18) else (1 / 2)))) else (if
    i.val < 71 then (if i.val < 69 then 0 else (if i.val < 70 then -1 else (-1 / 3))) else (if
    i.val < 73 then 0 else (if i.val < 74 then 0 else (-4 / 3)))))) else (if i.val < 88 then (if
    i.val < 81 then (if i.val < 78 then (if i.val < 76 then 0 else (if i.val < 77 then (1 / 3)
    else (10 / 9))) else (if i.val < 79 then -1 else 0)) else (if i.val < 84 then (if i.val < 82
    then (-2 / 3) else (if i.val < 83 then 0 else (1 / 3))) else (if i.val < 86 then (if i.val <
    85 then (10 / 9) else -1) else 0))) else (if i.val < 94 then (if i.val < 91 then (if i.val <
    89 then 2 else 0) else (if i.val < 92 then 0 else (if i.val < 93 then 0 else (-1 / 18))))
    else (if i.val < 97 then (if i.val < 95 then (1 / 2) else (if i.val < 96 then (-1 / 18) else
    (1 / 2))) else 0))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then
    (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then (-4 / 3) else 0) else (if
    i.val < 105 then 0 else (if i.val < 106 then (-4 / 3) else (-1 / 18)))) else (if i.val < 110
    then (if i.val < 108 then (-17 / 18) else (if i.val < 109 then (2 / 3) else (-1 / 3))) else
    (if i.val < 111 then (-1 / 3) else (if i.val < 112 then (2 / 3) else (-1 / 3))))) else (if
    i.val < 119 then (if i.val < 116 then (if i.val < 114 then (-1 / 3) else (if i.val < 115
    then (2 / 3) else (-17 / 18))) else (if i.val < 117 then (-1 / 18) else (if i.val < 118 then
    (-17 / 18) else (-1 / 18)))) else (if i.val < 122 then (if i.val < 120 then (-1 / 3) else
    (if i.val < 121 then (-1 / 3) else (1 / 15))) else (if i.val < 124 then (if i.val < 123 then
    (4259 / 3510) else (161 / 270)) else (if i.val < 125 then (-745 / 351) else (407 / 540))))))
    else (if i.val < 139 then (if i.val < 132 then (if i.val < 129 then (if i.val < 127 then
    (12553 / 23868) else (if i.val < 128 then (-193 / 1080) else (27371 / 14040))) else (if
    i.val < 130 then (-991 / 1404) else (if i.val < 131 then (791 / 390) else (-2797 / 3978))))
    else (if i.val < 135 then (if i.val < 133 then (-23 / 1080) else (if i.val < 134 then (899 /
    1080) else (701 / 1326))) else (if i.val < 137 then (if i.val < 136 then (6047 / 4680) else
    (559 / 1080)) else (if i.val < 138 then (-745 / 351) else (1 / 15))))) else (if i.val < 145
    then (if i.val < 142 then (if i.val < 140 then (3853 / 1989) else (3527 / 5265)) else (if
    i.val < 143 then (-1490 / 1053) else (if i.val < 144 then (7706 / 5967) else (3527 /
    5265)))) else (if i.val < 148 then (if i.val < 146 then (3527 / 5265) else (if i.val < 147
    then (-1490 / 1053) else (20933 / 21060))) else (if i.val < 150 then (if i.val < 149 then
    (-4229 / 71604) else (13913 / 21060)) else (if i.val < 151 then (-4229 / 71604) else (13913
    / 21060))))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val
    < 155 then (if i.val < 153 then (-4229 / 71604) else (if i.val < 154 then (20933 / 21060)
    else (-4229 / 71604))) else (if i.val < 156 then (3527 / 5265) else (if i.val < 157 then
    (3527 / 5265) else (-1490 / 1053)))) else (if i.val < 161 then (if i.val < 159 then (7706 /
    5967) else (3527 / 5265)) else (if i.val < 162 then (-1490 / 1053) else (if i.val < 163 then
    (20933 / 21060) else (-4229 / 71604))))) else (if i.val < 170 then (if i.val < 167 then (if
    i.val < 165 then (13913 / 21060) else (if i.val < 166 then (-4229 / 71604) else (13913 /
    21060))) else (if i.val < 168 then (-4229 / 71604) else (if i.val < 169 then (20933 / 21060)
    else (-4229 / 71604)))) else (if i.val < 173 then (if i.val < 171 then -1 else (-1 / 5))
    else (if i.val < 175 then (if i.val < 174 then (1481 / 1053) else (161 / 135)) else (if
    i.val < 176 then (-3050 / 1053) else (-1 / 5)))))) else (if i.val < 190 then (if i.val < 183
    then (if i.val < 180 then (if i.val < 178 then (-1 / 5) else (if i.val < 179 then (407 /
    270) else (-2203 / 11934))) else (if i.val < 181 then (4327 / 2106) else (if i.val < 182
    then (-133 / 2106) else (4259 / 3510)))) else (if i.val < 186 then (if i.val < 184 then (1 /
    15) else (if i.val < 185 then (161 / 270) else (-745 / 351))) else (if i.val < 188 then (if
    i.val < 187 then (407 / 540) else (12553 / 23868)) else (if i.val < 189 then (27371 / 14040)
    else (-193 / 1080))))) else (if i.val < 196 then (if i.val < 193 then (if i.val < 191 then
    (-991 / 1404) else (if i.val < 192 then (1 / 15) else (3853 / 1989))) else (if i.val < 194
    then (6047 / 4680) else (if i.val < 195 then (559 / 1080) else (-745 / 351)))) else (if
    i.val < 199 then (if i.val < 197 then (-23 / 1080) else (if i.val < 198 then (899 / 1080)
    else (701 / 1326))) else (if i.val < 201 then (if i.val < 200 then (791 / 390) else (-2797 /
    3978)) else (if i.val < 202 then (4259 / 3510) else (1 / 15))))))))) else (if i.val < 305
    then (if i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if
    i.val < 206 then (if i.val < 204 then (161 / 270) else (if i.val < 205 then (-745 / 351)
    else (407 / 540))) else (if i.val < 207 then (12553 / 23868) else (if i.val < 208 then
    (27371 / 14040) else (-193 / 1080)))) else (if i.val < 212 then (if i.val < 210 then (-991 /
    1404) else (if i.val < 211 then (1 / 15) else (3853 / 1989))) else (if i.val < 213 then
    (6047 / 4680) else (if i.val < 214 then (559 / 1080) else (-745 / 351))))) else (if i.val <
    221 then (if i.val < 218 then (if i.val < 216 then (-23 / 1080) else (if i.val < 217 then
    (899 / 1080) else (701 / 1326))) else (if i.val < 219 then (791 / 390) else (if i.val < 220
    then (-2797 / 3978) else (-1 / 15)))) else (if i.val < 224 then (if i.val < 222 then (-1 /
    15) else (if i.val < 223 then (-1 / 15) else (1285 / 468))) else (if i.val < 226 then (if
    i.val < 225 then (161 / 60) else (-745 / 117)) else (1 / 10))))) else (if i.val < 241 then
    (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then (1 / 10) else (if i.val < 230
    then (407 / 120) else (-953 / 1768))) else (if i.val < 232 then (4637 / 936) else (if i.val
    < 233 then (7 / 936) else (3527 / 5265)))) else (if i.val < 237 then (if i.val < 235 then
    (3527 / 5265) else (if i.val < 236 then (-1490 / 1053) else (7706 / 5967))) else (if i.val <
    239 then (3527 / 5265) else (if i.val < 240 then (-1490 / 1053) else (20933 / 21060)))))
    else (if i.val < 247 then (if i.val < 244 then (if i.val < 242 then (-4229 / 71604) else (if
    i.val < 243 then (13913 / 21060) else (-4229 / 71604))) else (if i.val < 245 then (13913 /
    21060) else (if i.val < 246 then (-4229 / 71604) else (20933 / 21060)))) else (if i.val <
    250 then (if i.val < 248 then (-4229 / 71604) else (if i.val < 249 then (-1 / 5) else -1))
    else (if i.val < 252 then (if i.val < 251 then (-1 / 5) else (1481 / 1053)) else (if i.val <
    253 then (161 / 135) else (-3050 / 1053))))))) else (if i.val < 279 then (if i.val < 266
    then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then (-1 / 5) else (if i.val
    < 256 then (-1 / 5) else (407 / 270))) else (if i.val < 258 then (-2203 / 11934) else (if
    i.val < 259 then (4327 / 2106) else (-133 / 2106)))) else (if i.val < 263 then (if i.val <
    261 then (-1 / 5) else (if i.val < 262 then -1 else (-1 / 5))) else (if i.val < 264 then
    (1481 / 1053) else (if i.val < 265 then (161 / 135) else (-3050 / 1053))))) else (if i.val <
    272 then (if i.val < 269 then (if i.val < 267 then (-1 / 5) else (if i.val < 268 then (-1 /
    5) else (407 / 270))) else (if i.val < 270 then (-2203 / 11934) else (if i.val < 271 then
    (4327 / 2106) else (-133 / 2106)))) else (if i.val < 275 then (if i.val < 273 then (-1 / 5)
    else (if i.val < 274 then (-9 / 5) else (-1 / 5))) else (if i.val < 277 then (if i.val < 276
    then (-1 / 5) else (4 / 5)) else (if i.val < 278 then (4 / 5) else (-1 / 15)))))) else (if
    i.val < 292 then (if i.val < 285 then (if i.val < 282 then (if i.val < 280 then (-1 / 15)
    else (if i.val < 281 then (1 / 3) else (3 / 5))) else (2 / 15)) else (if i.val < 288 then
    (if i.val < 286 then (-4 / 15) else (2 / 15)) else (if i.val < 290 then (if i.val < 289 then
    (-4 / 15) else (2 / 15)) else (if i.val < 291 then (2 / 15) else (-1 / 5))))) else (if i.val
    < 298 then (if i.val < 295 then (if i.val < 293 then (1 / 15) else (if i.val < 294 then (1 /
    15) else (-1 / 5))) else (if i.val < 296 then (4 / 5) else (-1 / 15))) else (if i.val < 301
    then (if i.val < 299 then (3 / 5) else (if i.val < 300 then (1 / 3) else (-1 / 15))) else
    (if i.val < 303 then (if i.val < 302 then (-1 / 15) else (3 / 5)) else (if i.val < 304 then
    (1 / 3) else (-1 / 15)))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val < 317
    then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then (-1 / 15) else (if i.val
    < 307 then (-1 / 15) else (-3 / 5))) else (if i.val < 309 then (-4 / 15) else (2 / 15)))
    else (if i.val < 314 then (if i.val < 312 then (1 / 15) else (if i.val < 313 then (-1 / 5)
    else (1 / 15))) else (if i.val < 315 then (-1 / 5) else (if i.val < 316 then (1 / 15) else
    (-1 / 5))))) else (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then (1 / 15)
    else (if i.val < 319 then (-1 / 5) else (1 / 30))) else (if i.val < 321 then (3 / 10) else
    (1 / 30))) else (if i.val < 326 then (if i.val < 324 then (-1 / 3) else (if i.val < 325 then
    (1 / 3) else (-1 / 5))) else (if i.val < 328 then (if i.val < 327 then (-8 / 15) else (2 /
    15)) else (if i.val < 329 then (2 / 15) else (-1 / 5)))))) else (if i.val < 343 then (if
    i.val < 336 then (if i.val < 333 then (if i.val < 331 then -1 else (if i.val < 332 then (1 /
    15) else (-1 / 5))) else (if i.val < 334 then (-1 / 3) else (if i.val < 335 then (-1 / 5)
    else (1 / 3)))) else (if i.val < 339 then (if i.val < 337 then (-1 / 3) else (-1 / 15)) else
    (if i.val < 341 then (if i.val < 340 then (-7 / 5) else (-1 / 5)) else (if i.val < 342 then
    (1 / 15) else -1)))) else (if i.val < 349 then (if i.val < 346 then (if i.val < 344 then (-1
    / 5) else (if i.val < 345 then (-1 / 3) else (1 / 3))) else (if i.val < 347 then (-1 / 5)
    else (if i.val < 348 then (-8 / 15) else (2 / 15)))) else (if i.val < 352 then (if i.val <
    350 then (2 / 15) else (if i.val < 351 then (-1 / 5) else -1)) else (if i.val < 354 then (if
    i.val < 353 then (1 / 15) else (-1 / 5)) else (if i.val < 355 then (-1 / 3) else (-1 /
    5))))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val < 359
    then (if i.val < 357 then (1 / 3) else (if i.val < 358 then (-1 / 3) else (-1 / 15))) else
    (if i.val < 360 then (-1 / 15) else (if i.val < 361 then (-7 / 5) else (2 / 15)))) else (if
    i.val < 365 then (if i.val < 363 then (2 / 15) else (if i.val < 364 then (-8 / 15) else (-6
    / 5))) else (if i.val < 366 then (-6 / 5) else (if i.val < 367 then (-6 / 5) else (-7 /
    5))))) else (if i.val < 374 then (if i.val < 371 then (if i.val < 369 then (-1 / 15) else
    (if i.val < 370 then (-1 / 15) else (-1 / 3))) else (if i.val < 372 then (-1 / 5) else (if
    i.val < 373 then (1 / 3) else (-1 / 3)))) else (if i.val < 377 then (if i.val < 375 then (-1
    / 5) else (if i.val < 376 then (1 / 3) else (-1 / 3))) else (if i.val < 379 then (-565 /
    351) else (if i.val < 380 then (-197 / 270) else (-47 / 45)))))) else (if i.val < 394 then
    (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then (-24779 / 10530) else (if
    i.val < 383 then (-52873 / 21060) else (-565 / 351))) else (if i.val < 385 then (-3527 /
    5265) else (if i.val < 386 then (-17423 / 21060) else (-3527 / 5265)))) else (if i.val < 390
    then (if i.val < 388 then (-17423 / 21060) else (if i.val < 389 then (-24779 / 10530) else
    (-52873 / 21060))) else (if i.val < 392 then (if i.val < 391 then (-1130 / 1053) else (-3527
    / 5265)) else (if i.val < 393 then (-17423 / 21060) else (-3527 / 5265))))) else (if i.val <
    400 then (if i.val < 397 then (if i.val < 395 then (-17423 / 21060) else (if i.val < 396
    then (-24779 / 10530) else (-52873 / 21060))) else (if i.val < 398 then (-1130 / 1053) else
    (if i.val < 399 then (-2105 / 1053) else (-197 / 270)))) else (if i.val < 403 then (if i.val
    < 401 then (-47 / 45) else (-565 / 351)) else (if i.val < 405 then (if i.val < 404 then
    (-565 / 351) else (-197 / 270)) else (if i.val < 406 then (-47 / 45) else (-565 /
    351)))))))))) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val
    < 432 then (if i.val < 419 then (if i.val < 413 then (if i.val < 410 then (if i.val < 408
    then (-565 / 351) else (if i.val < 409 then (-565 / 351) else (-565 / 117))) else (if i.val
    < 411 then (-3527 / 5265) else (if i.val < 412 then (-17423 / 21060) else (-3527 / 5265))))
    else (if i.val < 416 then (if i.val < 414 then (-17423 / 21060) else (if i.val < 415 then
    (-1130 / 1053) else (-2105 / 1053))) else (if i.val < 417 then (-2105 / 1053) else (if i.val
    < 418 then (-1199 / 59670) else (-8909 / 59670))))) else (if i.val < 425 then (if i.val <
    422 then (if i.val < 420 then (-73 / 195) else (if i.val < 421 then (1106 / 5967) else (-809
    / 59670))) else (if i.val < 423 then (-547 / 3510) else (if i.val < 424 then (-73 / 390)
    else (-343 / 2340)))) else (if i.val < 428 then (if i.val < 426 then (4229 / 23868) else (if
    i.val < 427 then (-2723 / 119340) else (2212 / 17901))) else (-5054 / 89505)))) else (if
    i.val < 445 then (if i.val < 438 then (if i.val < 435 then (if i.val < 433 then (-146 / 585)
    else (if i.val < 434 then (-73 / 585) else (-5054 / 89505))) else (if i.val < 436 then
    (-5054 / 89505) else (if i.val < 437 then (4229 / 35802) else (2212 / 17901)))) else (if
    i.val < 441 then (-5054 / 89505) else (if i.val < 443 then (if i.val < 442 then (-5054 /
    89505) else (-146 / 585)) else (if i.val < 444 then (-73 / 585) else (-5054 / 89505)))))
    else (if i.val < 451 then (if i.val < 448 then (if i.val < 446 then (-5054 / 89505) else (if
    i.val < 447 then (4229 / 35802) else (-13627 / 89505))) else (if i.val < 449 then (-178 /
    1755) else (if i.val < 450 then (-7 / 26) else (-1199 / 59670)))) else (if i.val < 454 then
    (if i.val < 452 then (1106 / 5967) else (if i.val < 453 then (-809 / 59670) else (-8909 /
    59670))) else (if i.val < 456 then (if i.val < 455 then (-73 / 195) else (-547 / 3510)) else
    (if i.val < 457 then (-73 / 390) else (4229 / 23868))))))) else (if i.val < 483 then (if
    i.val < 470 then (if i.val < 464 then (if i.val < 461 then (if i.val < 459 then (-343 /
    2340) else (if i.val < 460 then (-2723 / 119340) else (-1199 / 59670))) else (if i.val < 462
    then (1106 / 5967) else (if i.val < 463 then (-809 / 59670) else (-8909 / 59670)))) else (if
    i.val < 467 then (if i.val < 465 then (-73 / 195) else (if i.val < 466 then (-547 / 3510)
    else (-73 / 390))) else (if i.val < 468 then (4229 / 23868) else (if i.val < 469 then (-343
    / 2340) else (-2723 / 119340))))) else (if i.val < 476 then (if i.val < 473 then (if i.val <
    471 then (-14657 / 39780) else (if i.val < 472 then (-109 / 780) else (-73 / 130))) else (if
    i.val < 474 then (2212 / 17901) else (-5054 / 89505))) else (if i.val < 479 then (if i.val <
    477 then (-5054 / 89505) else (if i.val < 478 then (-5054 / 89505) else (-146 / 585))) else
    (if i.val < 481 then (if i.val < 480 then (-73 / 585) else (-5054 / 89505)) else (if i.val <
    482 then (-5054 / 89505) else (4229 / 35802)))))) else (if i.val < 496 then (if i.val < 489
    then (if i.val < 486 then (if i.val < 484 then (-13627 / 89505) else (if i.val < 485 then
    (-178 / 1755) else (-7 / 26))) else (if i.val < 487 then (-13627 / 89505) else (if i.val <
    488 then (-178 / 1755) else (-7 / 26)))) else (if i.val < 492 then (if i.val < 490 then
    (3853 / 1989) else (7706 / 5967)) else (if i.val < 494 then (if i.val < 493 then (15740 /
    5967) else (3853 / 1989)) else (if i.val < 495 then (3853 / 1989) else (3853 / 663))))) else
    (if i.val < 502 then (if i.val < 499 then (if i.val < 497 then (7706 / 5967) else (15740 /
    5967)) else (if i.val < 500 then (-539 / 5616) else (if i.val < 501 then (1 / 360) else (101
    / 1560)))) else (if i.val < 505 then (if i.val < 503 then (67 / 2160) else (if i.val < 504
    then (-539 / 8424) else (2923 / 84240))) else (if i.val < 507 then (if i.val < 506 then
    (2923 / 84240) else (-539 / 8424)) else (2923 / 84240))))))) else (if i.val < 560 then (if
    i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val <
    510 then (-1085 / 8424) else (if i.val < 511 then (-1 / 24) else (-1 / 120))) else (if i.val
    < 513 then (-1 / 120) else (if i.val < 514 then (76 / 1053) else (67 / 1080)))) else (if
    i.val < 518 then (if i.val < 516 then (-539 / 5616) else (if i.val < 517 then (101 / 1560)
    else (1 / 360))) else (if i.val < 519 then (67 / 2160) else (if i.val < 520 then (-539 /
    5616) else (101 / 1560))))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
    then (1 / 360) else (if i.val < 523 then (67 / 2160) else (-539 / 1872))) else (-1 / 360))
    else (if i.val < 530 then (if i.val < 528 then (553 / 3744) else (if i.val < 529 then (67 /
    480) else (-539 / 8424))) else (if i.val < 532 then (2923 / 84240) else (if i.val < 533 then
    (-1085 / 8424) else (-1 / 120)))))) else (if i.val < 547 then (if i.val < 540 then (if i.val
    < 537 then (if i.val < 535 then (-1 / 24) else (if i.val < 536 then (-1 / 120) else (76 /
    1053))) else (if i.val < 538 then (67 / 1080) else (if i.val < 539 then (-1085 / 8424) else
    (-1 / 120)))) else (if i.val < 543 then (if i.val < 541 then (-1 / 24) else (if i.val < 542
    then (-1 / 120) else (76 / 1053))) else (if i.val < 545 then (if i.val < 544 then (67 /
    1080) else (-1 / 120)) else (if i.val < 546 then (-3 / 40) else (-1 / 120))))) else (if
    i.val < 553 then (if i.val < 550 then (if i.val < 548 then (-1 / 120) else (1 / 30)) else
    (if i.val < 551 then (-1 / 60) else (if i.val < 552 then (-1 / 60) else (1 / 36)))) else (if
    i.val < 556 then (if i.val < 554 then (-1 / 60) else (1 / 180)) else (if i.val < 558 then
    (if i.val < 557 then (1 / 180) else (-1 / 12)) else (if i.val < 559 then (-7 / 180) else (1
    / 180))))))) else (if i.val < 585 then (if i.val < 572 then (if i.val < 566 then (if i.val <
    563 then (if i.val < 561 then (1 / 180) else (if i.val < 562 then (-1 / 12) else (-7 /
    180))) else (if i.val < 564 then (1 / 180) else (if i.val < 565 then (1 / 180) else (-1 /
    20)))) else (if i.val < 569 then (if i.val < 567 then (1 / 60) else (if i.val < 568 then (1
    / 60) else (-1 / 20))) else (if i.val < 570 then (1 / 30) else (-1 / 60)))) else (if i.val <
    578 then (if i.val < 575 then (if i.val < 573 then (-1 / 60) else (if i.val < 574 then (1 /
    36) else (-1 / 60))) else (if i.val < 576 then (-1 / 60) else (if i.val < 577 then (-1 / 60)
    else (1 / 36)))) else (if i.val < 581 then (-1 / 60) else (if i.val < 583 then (if i.val <
    582 then (-3 / 20) else (-7 / 180)) else (if i.val < 584 then (-1 / 12) else (1 / 180))))))
    else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then (if i.val < 586 then (1
    / 180) else (if i.val < 587 then (1 / 60) else (-1 / 20))) else (if i.val < 589 then (1 /
    60) else (if i.val < 590 then (-1 / 20) else (1 / 60)))) else (if i.val < 594 then (if i.val
    < 592 then (-1 / 20) else (if i.val < 593 then (1 / 60) else (-1 / 20))) else (if i.val <
    596 then (if i.val < 595 then (1 / 60) else (3 / 20)) else (1 / 60)))) else (if i.val < 604
    then (if i.val < 601 then (if i.val < 599 then (-1 / 720) else (if i.val < 600 then (-1 /
    80) else (-1 / 720))) else (if i.val < 602 then (-1 / 720) else (if i.val < 603 then (7 /
    720) else (-1 / 720)))) else (if i.val < 607 then (if i.val < 605 then (1 / 48) else (if
    i.val < 606 then (-1 / 720) else (7 / 720))) else (if i.val < 609 then (if i.val < 608 then
    (-1 / 720) else (1 / 48)) else (if i.val < 610 then (-1 / 720) else (-1 / 240))))))))) else
    (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val < 623 then (if
    i.val < 617 then (if i.val < 614 then (if i.val < 612 then (-1 / 240) else (1 / 80)) else
    (if i.val < 615 then (3 / 80) else (1 / 240))) else (if i.val < 620 then (if i.val < 618
    then (1 / 240) else (-1 / 80)) else (if i.val < 621 then (1 / 240) else (if i.val < 622 then
    (1 / 240) else (-1 / 80))))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624
    then (-1 / 80) else (1 / 240)) else (if i.val < 627 then (-1 / 48) else (1 / 720))) else (if
    i.val < 632 then (if i.val < 630 then (-7 / 720) else (if i.val < 631 then (7 / 720) else (1
    / 48))) else (if i.val < 634 then (-1 / 720) else (-1 / 240))))) else (if i.val < 649 then
    (if i.val < 642 then (if i.val < 639 then (if i.val < 637 then (1 / 80) else (if i.val < 638
    then (1 / 80) else (-1 / 240))) else (if i.val < 640 then (-1 / 240) else (1 / 80))) else
    (if i.val < 645 then (-1 / 240) else (if i.val < 647 then (if i.val < 646 then (-3 / 80)
    else (-1 / 80)) else (if i.val < 648 then (-1 / 80) else (1 / 240))))) else (if i.val < 655
    then (if i.val < 652 then (if i.val < 650 then (1 / 240) else (if i.val < 651 then (1 / 720)
    else (-1 / 48))) else (if i.val < 653 then (1 / 720) else (if i.val < 654 then (-7 / 720)
    else (1 / 720)))) else (if i.val < 658 then (if i.val < 656 then (-1 / 48) else (if i.val <
    657 then (1 / 720) else (-7 / 720))) else (if i.val < 660 then (if i.val < 659 then (1 /
    720) else (1 / 80)) else (1 / 720)))))) else (if i.val < 687 then (if i.val < 674 then (if
    i.val < 668 then (if i.val < 665 then (if i.val < 663 then (-491 / 5616) else (if i.val <
    664 then (-79 / 2160) else (-5299 / 42120))) else (if i.val < 666 then (-491 / 5616) else
    (if i.val < 667 then (641 / 28080) else (-629 / 28080)))) else (if i.val < 671 then (if
    i.val < 669 then (-5023 / 28080) else (if i.val < 670 then (539 / 5616) else (1421 /
    28080))) else (if i.val < 672 then (-1409 / 28080) else (if i.val < 673 then (-5023 / 28080)
    else (4637 / 238680))))) else (if i.val < 680 then (if i.val < 677 then (if i.val < 675 then
    (83 / 17680) else (if i.val < 676 then (-2077 / 238680) else (-227 / 9360))) else (if i.val
    < 678 then (4637 / 238680) else (if i.val < 679 then (2371 / 477360) else (-7 / 780)))) else
    (if i.val < 683 then (if i.val < 681 then (-227 / 9360) else (-2923 / 84240)) else (if i.val
    < 685 then (if i.val < 684 then (-5299 / 42120) else (-491 / 8424)) else (if i.val < 686
    then (539 / 8424) else (1 / 7020)))))) else (if i.val < 700 then (if i.val < 693 then (if
    i.val < 690 then (1 / 7020) else (if i.val < 691 then (-5023 / 42120) else (if i.val < 692
    then (-5023 / 42120) else (4637 / 358020)))) else (if i.val < 696 then (if i.val < 694 then
    (4637 / 358020) else (-1913 / 1432080)) else (if i.val < 698 then (-1913 / 1432080) else
    (-227 / 14040)))) else (if i.val < 706 then (if i.val < 703 then (if i.val < 701 then (-2923
    / 84240) else (if i.val < 702 then (-2923 / 84240) else (-5299 / 42120))) else (if i.val <
    704 then (-491 / 8424) else (if i.val < 705 then (539 / 8424) else (1 / 7020)))) else (if
    i.val < 709 then (1 / 7020) else (if i.val < 711 then (-5023 / 42120) else (4637 /
    358020))))))) else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val
    < 719 then (if i.val < 716 then (-1913 / 1432080) else (if i.val < 717 then (-1913 /
    1432080) else (-227 / 14040))) else (if i.val < 722 then (if i.val < 720 then (-115 / 1053)
    else (if i.val < 721 then (-737 / 42120) else (47 / 42120))) else (if i.val < 723 then
    (-2159 / 8424) else (if i.val < 724 then (7399 / 286416) else (-5203 / 1432080))))) else (if
    i.val < 731 then (if i.val < 728 then (if i.val < 726 then (-77 / 28080) else (if i.val <
    727 then (-187 / 5616) else (-79 / 2160))) else (if i.val < 729 then (-491 / 5616) else (if
    i.val < 730 then (-491 / 5616) else (641 / 28080)))) else (if i.val < 734 then (if i.val <
    732 then (539 / 5616) else (if i.val < 733 then (1421 / 28080) else (-629 / 28080))) else
    (if i.val < 736 then (if i.val < 735 then (-5023 / 28080) else (-1409 / 28080)) else (if
    i.val < 737 then (-5023 / 28080) else (4637 / 238680)))))) else (if i.val < 751 then (if
    i.val < 744 then (if i.val < 741 then (if i.val < 739 then (83 / 17680) else (if i.val < 740
    then (4637 / 238680) else (2371 / 477360))) else (if i.val < 742 then (-2077 / 238680) else
    (if i.val < 743 then (-227 / 9360) else (-7 / 780)))) else (if i.val < 747 then (if i.val <
    745 then (-227 / 9360) else (if i.val < 746 then (-79 / 2160) else (-491 / 5616))) else (if
    i.val < 749 then (if i.val < 748 then (-491 / 5616) else (641 / 28080)) else (if i.val < 750
    then (539 / 5616) else (1421 / 28080))))) else (if i.val < 757 then (if i.val < 754 then (if
    i.val < 752 then (-629 / 28080) else (if i.val < 753 then (-5023 / 28080) else (-1409 /
    28080))) else (if i.val < 755 then (-5023 / 28080) else (if i.val < 756 then (4637 / 238680)
    else (83 / 17680)))) else (if i.val < 760 then (if i.val < 758 then (4637 / 238680) else (if
    i.val < 759 then (2371 / 477360) else (-2077 / 238680))) else (if i.val < 762 then (if i.val
    < 761 then (-227 / 9360) else (-7 / 780)) else (if i.val < 763 then (-227 / 9360) else (-491
    / 1872))))))) else (if i.val < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val
    < 767 then (if i.val < 765 then (-193 / 4680) else (if i.val < 766 then (199 / 4680) else
    (-5023 / 9360))) else (if i.val < 768 then (4637 / 79560) else (if i.val < 769 then (-2551 /
    318240) else (-5 / 1248)))) else (if i.val < 773 then (if i.val < 771 then (-227 / 3120)
    else (-2923 / 84240)) else (if i.val < 774 then (-491 / 8424) else (if i.val < 775 then (539
    / 8424) else (1 / 7020))))) else (if i.val < 782 then (if i.val < 779 then (1 / 7020) else
    (if i.val < 780 then (-5023 / 42120) else (if i.val < 781 then (-5023 / 42120) else (4637 /
    358020)))) else (if i.val < 785 then (if i.val < 783 then (4637 / 358020) else (-1913 /
    1432080)) else (if i.val < 787 then (-1913 / 1432080) else (-227 / 14040))))) else (if i.val
    < 802 then (if i.val < 795 then (if i.val < 792 then (if i.val < 790 then (-115 / 1053) else
    (if i.val < 791 then (-737 / 42120) else (47 / 42120))) else (if i.val < 793 then (-2159 /
    8424) else (if i.val < 794 then (7399 / 286416) else (-5203 / 1432080)))) else (if i.val <
    798 then (if i.val < 796 then (-77 / 28080) else (if i.val < 797 then (-187 / 5616) else
    (-115 / 1053))) else (if i.val < 800 then (if i.val < 799 then (-737 / 42120) else (47 /
    42120)) else (if i.val < 801 then (-2159 / 8424) else (7399 / 286416))))) else (if i.val <
    808 then (if i.val < 805 then (if i.val < 803 then (-5203 / 1432080) else (if i.val < 804
    then (-77 / 28080) else (-187 / 5616))) else (if i.val < 806 then (-77 / 112320) else (-77 /
    168480))) else (if i.val < 811 then (if i.val < 809 then (-31 / 33696) else (-77 / 112320))
    else (if i.val < 813 then (if i.val < 812 then (-77 / 37440) else (-77 / 168480)) else (-31
    / 33696))))))))))

end AxiomaticGW.L24CorrectionsReplay
