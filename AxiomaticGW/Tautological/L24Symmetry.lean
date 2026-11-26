/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Graphs
public import AxiomaticGW.Tautological.StrataOperationReplay
public import AxiomaticGW.Tautological.GraphIsomorphismHint

/-!
# Label symmetry used in L24

Average over all six permutations fixing marking 1 (the second marking in
the paper). The finite destination permutations are checked on complete
decorated graphs, and coefficient transport follows by inverse reindexing.
-/

@[expose] public section

namespace AxiomaticGW.L24Symmetry
open RelationCertificate

set_option maxRecDepth 20000

/-- The 0-th permutation of the three free markings; old labels map covariantly. -/
def labels0 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A candidate bijection of the held frame columns. -/
def destination0 : Equiv.Perm (Fin 815) where
  toFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 0 else (if i.val < 2 then 1 else 2)) else (if i.val < 4 then 3 else (if i.val < 5
      then 4 else 5))) else (if i.val < 9 then (if i.val < 7 then 6 else (if i.val < 8 then 7
      else 8)) else (if i.val < 10 then 9 else (if i.val < 11 then 10 else 11)))) else (if i.val
      < 18 then (if i.val < 15 then (if i.val < 13 then 12 else (if i.val < 14 then 13 else 14))
      else (if i.val < 16 then 15 else (if i.val < 17 then 16 else 17))) else (if i.val < 21
      then (if i.val < 19 then 18 else (if i.val < 20 then 19 else 20)) else (if i.val < 23 then
      (if i.val < 22 then 21 else 22) else (if i.val < 24 then 23 else 24))))) else (if i.val <
      37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 25 else (if i.val < 27
      then 26 else 27)) else (if i.val < 29 then 28 else (if i.val < 30 then 29 else 30))) else
      (if i.val < 34 then (if i.val < 32 then 31 else (if i.val < 33 then 32 else 33)) else (if
      i.val < 35 then 34 else (if i.val < 36 then 35 else 36)))) else (if i.val < 43 then (if
      i.val < 40 then (if i.val < 38 then 37 else (if i.val < 39 then 38 else 39)) else (if
      i.val < 41 then 40 else (if i.val < 42 then 41 else 42))) else (if i.val < 46 then (if
      i.val < 44 then 43 else (if i.val < 45 then 44 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 46 else 47) else (if i.val < 49 then 48 else 49)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 50
      else (if i.val < 52 then 51 else 52)) else (if i.val < 54 then 53 else (if i.val < 55 then
      54 else 55))) else (if i.val < 59 then (if i.val < 57 then 56 else (if i.val < 58 then 57
      else 58)) else (if i.val < 60 then 59 else (if i.val < 61 then 60 else 61)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 62 else (if i.val < 64 then 63
      else 64)) else (if i.val < 66 then 65 else (if i.val < 67 then 66 else 67))) else (if
      i.val < 71 then (if i.val < 69 then 68 else (if i.val < 70 then 69 else 70)) else (if
      i.val < 73 then (if i.val < 72 then 71 else 72) else (if i.val < 74 then 73 else 74)))))
      else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then 75
      else (if i.val < 77 then 76 else 77)) else (if i.val < 79 then 78 else (if i.val < 80 then
      79 else 80))) else (if i.val < 84 then (if i.val < 82 then 81 else (if i.val < 83 then 82
      else 83)) else (if i.val < 86 then (if i.val < 85 then 84 else 85) else (if i.val < 87
      then 86 else 87)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then 88
      else (if i.val < 90 then 89 else 90)) else (if i.val < 92 then 91 else (if i.val < 93 then
      92 else 93))) else (if i.val < 97 then (if i.val < 95 then 94 else (if i.val < 96 then 95
      else 96)) else (if i.val < 99 then (if i.val < 98 then 97 else 98) else (if i.val < 100
      then 99 else 100))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113
      then (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 101 else (if i.val <
      103 then 102 else 103)) else (if i.val < 105 then 104 else (if i.val < 106 then 105 else
      106))) else (if i.val < 110 then (if i.val < 108 then 107 else (if i.val < 109 then 108
      else 109)) else (if i.val < 111 then 110 else (if i.val < 112 then 111 else 112)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 113 else (if i.val < 115
      then 114 else 115)) else (if i.val < 117 then 116 else (if i.val < 118 then 117 else
      118))) else (if i.val < 122 then (if i.val < 120 then 119 else (if i.val < 121 then 120
      else 121)) else (if i.val < 124 then (if i.val < 123 then 122 else 123) else (if i.val <
      125 then 124 else 125))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 126 else (if i.val < 128 then 127 else 128)) else (if i.val <
      130 then 129 else (if i.val < 131 then 130 else 131))) else (if i.val < 135 then (if i.val
      < 133 then 132 else (if i.val < 134 then 133 else 134)) else (if i.val < 137 then (if
      i.val < 136 then 135 else 136) else (if i.val < 138 then 137 else 138)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 139 else (if i.val < 141 then 140 else
      141)) else (if i.val < 143 then 142 else (if i.val < 144 then 143 else 144))) else (if
      i.val < 148 then (if i.val < 146 then 145 else (if i.val < 147 then 146 else 147)) else
      (if i.val < 150 then (if i.val < 149 then 148 else 149) else (if i.val < 151 then 150 else
      151)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 152 else (if i.val < 154 then 153 else 154)) else (if i.val
      < 156 then 155 else (if i.val < 157 then 156 else 157))) else (if i.val < 161 then (if
      i.val < 159 then 158 else (if i.val < 160 then 159 else 160)) else (if i.val < 162 then
      161 else (if i.val < 163 then 162 else 163)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 164 else (if i.val < 166 then 165 else 166)) else (if i.val <
      168 then 167 else (if i.val < 169 then 168 else 169))) else (if i.val < 173 then (if i.val
      < 171 then 170 else (if i.val < 172 then 171 else 172)) else (if i.val < 175 then (if
      i.val < 174 then 173 else 174) else (if i.val < 176 then 175 else 176))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 177 else (if
      i.val < 179 then 178 else 179)) else (if i.val < 181 then 180 else (if i.val < 182 then
      181 else 182))) else (if i.val < 186 then (if i.val < 184 then 183 else (if i.val < 185
      then 184 else 185)) else (if i.val < 188 then (if i.val < 187 then 186 else 187) else (if
      i.val < 189 then 188 else 189)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 190 else (if i.val < 192 then 191 else 192)) else (if i.val < 194 then 193 else
      (if i.val < 195 then 194 else 195))) else (if i.val < 199 then (if i.val < 197 then 196
      else (if i.val < 198 then 197 else 198)) else (if i.val < 201 then (if i.val < 200 then
      199 else 200) else (if i.val < 202 then 201 else 202)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 203 else (if i.val < 205 then 204 else 205)) else (if
      i.val < 207 then 206 else (if i.val < 208 then 207 else 208))) else (if i.val < 212 then
      (if i.val < 210 then 209 else (if i.val < 211 then 210 else 211)) else (if i.val < 213
      then 212 else (if i.val < 214 then 213 else 214)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 215 else (if i.val < 217 then 216 else 217)) else (if i.val
      < 219 then 218 else (if i.val < 220 then 219 else 220))) else (if i.val < 224 then (if
      i.val < 222 then 221 else (if i.val < 223 then 222 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 226 else 227))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 228 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 233))) else (if i.val < 237 then (if i.val < 235 then 234 else (if i.val <
      236 then 235 else 236)) else (if i.val < 239 then (if i.val < 238 then 237 else 238) else
      (if i.val < 240 then 239 else 240)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 241 else (if i.val < 243 then 242 else 243)) else (if i.val < 245 then
      244 else (if i.val < 246 then 245 else 246))) else (if i.val < 250 then (if i.val < 248
      then 247 else (if i.val < 249 then 248 else 249)) else (if i.val < 252 then (if i.val <
      251 then 250 else 251) else (if i.val < 253 then 252 else 253)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      254 else (if i.val < 256 then 255 else 256)) else (if i.val < 258 then 257 else (if i.val
      < 259 then 258 else 259))) else (if i.val < 263 then (if i.val < 261 then 260 else (if
      i.val < 262 then 261 else 262)) else (if i.val < 264 then 263 else (if i.val < 265 then
      264 else 265)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 266
      else (if i.val < 268 then 267 else 268)) else (if i.val < 270 then 269 else (if i.val <
      271 then 270 else 271))) else (if i.val < 275 then (if i.val < 273 then 272 else (if i.val
      < 274 then 273 else 274)) else (if i.val < 277 then (if i.val < 276 then 275 else 276)
      else (if i.val < 278 then 277 else 278))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 279 else (if i.val < 281 then 280 else 281))
      else (if i.val < 283 then 282 else (if i.val < 284 then 283 else 284))) else (if i.val <
      288 then (if i.val < 286 then 285 else (if i.val < 287 then 286 else 287)) else (if i.val
      < 290 then (if i.val < 289 then 288 else 289) else (if i.val < 291 then 290 else 291))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 292 else (if i.val <
      294 then 293 else 294)) else (if i.val < 296 then 295 else (if i.val < 297 then 296 else
      297))) else (if i.val < 301 then (if i.val < 299 then 298 else (if i.val < 300 then 299
      else 300)) else (if i.val < 303 then (if i.val < 302 then 301 else 302) else (if i.val <
      304 then 303 else 304))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 305 else (if i.val
      < 307 then 306 else 307)) else (if i.val < 309 then 308 else (if i.val < 310 then 309 else
      310))) else (if i.val < 314 then (if i.val < 312 then 311 else (if i.val < 313 then 312
      else 313)) else (if i.val < 315 then 314 else (if i.val < 316 then 315 else 316)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 317 else (if i.val < 319
      then 318 else 319)) else (if i.val < 321 then 320 else (if i.val < 322 then 321 else
      322))) else (if i.val < 326 then (if i.val < 324 then 323 else (if i.val < 325 then 324
      else 325)) else (if i.val < 328 then (if i.val < 327 then 326 else 327) else (if i.val <
      329 then 328 else 329))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 330 else (if i.val < 332 then 331 else 332)) else (if i.val <
      334 then 333 else (if i.val < 335 then 334 else 335))) else (if i.val < 339 then (if i.val
      < 337 then 336 else (if i.val < 338 then 337 else 338)) else (if i.val < 341 then (if
      i.val < 340 then 339 else 340) else (if i.val < 342 then 341 else 342)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 343 else (if i.val < 345 then 344 else
      345)) else (if i.val < 347 then 346 else (if i.val < 348 then 347 else 348))) else (if
      i.val < 352 then (if i.val < 350 then 349 else (if i.val < 351 then 350 else 351)) else
      (if i.val < 354 then (if i.val < 353 then 352 else 353) else (if i.val < 355 then 354 else
      355)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 356 else (if i.val < 358 then 357 else 358)) else (if i.val
      < 360 then 359 else (if i.val < 361 then 360 else 361))) else (if i.val < 365 then (if
      i.val < 363 then 362 else (if i.val < 364 then 363 else 364)) else (if i.val < 366 then
      365 else (if i.val < 367 then 366 else 367)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 368 else (if i.val < 370 then 369 else 370)) else (if i.val <
      372 then 371 else (if i.val < 373 then 372 else 373))) else (if i.val < 377 then (if i.val
      < 375 then 374 else (if i.val < 376 then 375 else 376)) else (if i.val < 379 then (if
      i.val < 378 then 377 else 378) else (if i.val < 380 then 379 else 380))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 381 else (if
      i.val < 383 then 382 else 383)) else (if i.val < 385 then 384 else (if i.val < 386 then
      385 else 386))) else (if i.val < 390 then (if i.val < 388 then 387 else (if i.val < 389
      then 388 else 389)) else (if i.val < 392 then (if i.val < 391 then 390 else 391) else (if
      i.val < 393 then 392 else 393)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 394 else (if i.val < 396 then 395 else 396)) else (if i.val < 398 then 397 else
      (if i.val < 399 then 398 else 399))) else (if i.val < 403 then (if i.val < 401 then 400
      else (if i.val < 402 then 401 else 402)) else (if i.val < 405 then (if i.val < 404 then
      403 else 404) else (if i.val < 406 then 405 else 406))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 407 else (if i.val < 409 then
      408 else 409)) else (if i.val < 411 then 410 else (if i.val < 412 then 411 else 412)))
      else (if i.val < 416 then (if i.val < 414 then 413 else (if i.val < 415 then 414 else
      415)) else (if i.val < 417 then 416 else (if i.val < 418 then 417 else 418)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 419 else (if i.val < 421 then
      420 else 421)) else (if i.val < 423 then 422 else (if i.val < 424 then 423 else 424)))
      else (if i.val < 428 then (if i.val < 426 then 425 else (if i.val < 427 then 426 else
      427)) else (if i.val < 430 then (if i.val < 429 then 428 else 429) else (if i.val < 431
      then 430 else 431))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 432 else (if i.val < 434 then 433 else 434)) else (if i.val < 436
      then 435 else (if i.val < 437 then 436 else 437))) else (if i.val < 441 then (if i.val <
      439 then 438 else (if i.val < 440 then 439 else 440)) else (if i.val < 443 then (if i.val
      < 442 then 441 else 442) else (if i.val < 444 then 443 else 444)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 445 else (if i.val < 447 then 446 else
      447)) else (if i.val < 449 then 448 else (if i.val < 450 then 449 else 450))) else (if
      i.val < 454 then (if i.val < 452 then 451 else (if i.val < 453 then 452 else 453)) else
      (if i.val < 456 then (if i.val < 455 then 454 else 455) else (if i.val < 457 then 456 else
      457)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 458 else (if i.val < 460 then 459 else 460)) else (if i.val
      < 462 then 461 else (if i.val < 463 then 462 else 463))) else (if i.val < 467 then (if
      i.val < 465 then 464 else (if i.val < 466 then 465 else 466)) else (if i.val < 468 then
      467 else (if i.val < 469 then 468 else 469)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 473 else (if i.val < 475 then 474 else 475))) else (if i.val < 479 then (if i.val
      < 477 then 476 else (if i.val < 478 then 477 else 478)) else (if i.val < 481 then (if
      i.val < 480 then 479 else 480) else (if i.val < 482 then 481 else 482))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 483 else (if
      i.val < 485 then 484 else 485)) else (if i.val < 487 then 486 else (if i.val < 488 then
      487 else 488))) else (if i.val < 492 then (if i.val < 490 then 489 else (if i.val < 491
      then 490 else 491)) else (if i.val < 494 then (if i.val < 493 then 492 else 493) else (if
      i.val < 495 then 494 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 496 else (if i.val < 498 then 497 else 498)) else (if i.val < 500 then 499 else
      (if i.val < 501 then 500 else 501))) else (if i.val < 505 then (if i.val < 503 then 502
      else (if i.val < 504 then 503 else 504)) else (if i.val < 507 then (if i.val < 506 then
      505 else 506) else (if i.val < 508 then 507 else 508))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 509 else (if i.val < 511 then 510 else 511)) else (if i.val < 513 then 512 else
      (if i.val < 514 then 513 else 514))) else (if i.val < 518 then (if i.val < 516 then 515
      else (if i.val < 517 then 516 else 517)) else (if i.val < 519 then 518 else (if i.val <
      520 then 519 else 520)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 521 else (if i.val < 523 then 522 else 523)) else (if i.val < 525 then 524 else (if
      i.val < 526 then 525 else 526))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 529)) else (if i.val < 532 then (if i.val < 531 then 530
      else 531) else (if i.val < 533 then 532 else 533))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 534 else (if i.val < 536 then 535
      else 536)) else (if i.val < 538 then 537 else (if i.val < 539 then 538 else 539))) else
      (if i.val < 543 then (if i.val < 541 then 540 else (if i.val < 542 then 541 else 542))
      else (if i.val < 545 then (if i.val < 544 then 543 else 544) else (if i.val < 546 then 545
      else 546)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 547 else
      (if i.val < 549 then 548 else 549)) else (if i.val < 551 then 550 else (if i.val < 552
      then 551 else 552))) else (if i.val < 556 then (if i.val < 554 then 553 else (if i.val <
      555 then 554 else 555)) else (if i.val < 558 then (if i.val < 557 then 556 else 557) else
      (if i.val < 559 then 558 else 559)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 560 else (if i.val < 562 then
      561 else 562)) else (if i.val < 564 then 563 else (if i.val < 565 then 564 else 565)))
      else (if i.val < 569 then (if i.val < 567 then 566 else (if i.val < 568 then 567 else
      568)) else (if i.val < 570 then 569 else (if i.val < 571 then 570 else 571)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 572 else (if i.val < 574 then
      573 else 574)) else (if i.val < 576 then 575 else (if i.val < 577 then 576 else 577)))
      else (if i.val < 581 then (if i.val < 579 then 578 else (if i.val < 580 then 579 else
      580)) else (if i.val < 583 then (if i.val < 582 then 581 else 582) else (if i.val < 584
      then 583 else 584))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 585 else (if i.val < 587 then 586 else 587)) else (if i.val < 589
      then 588 else (if i.val < 590 then 589 else 590))) else (if i.val < 594 then (if i.val <
      592 then 591 else (if i.val < 593 then 592 else 593)) else (if i.val < 596 then (if i.val
      < 595 then 594 else 595) else (if i.val < 597 then 596 else 597)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 598 else (if i.val < 600 then 599 else
      600)) else (if i.val < 602 then 601 else (if i.val < 603 then 602 else 603))) else (if
      i.val < 607 then (if i.val < 605 then 604 else (if i.val < 606 then 605 else 606)) else
      (if i.val < 609 then (if i.val < 608 then 607 else 608) else (if i.val < 610 then 609 else
      610)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 611 else (if
      i.val < 613 then 612 else 613)) else (if i.val < 615 then 614 else (if i.val < 616 then
      615 else 616))) else (if i.val < 620 then (if i.val < 618 then 617 else (if i.val < 619
      then 618 else 619)) else (if i.val < 621 then 620 else (if i.val < 622 then 621 else
      622)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 623 else (if
      i.val < 625 then 624 else 625)) else (if i.val < 627 then 626 else (if i.val < 628 then
      627 else 628))) else (if i.val < 632 then (if i.val < 630 then 629 else (if i.val < 631
      then 630 else 631)) else (if i.val < 634 then (if i.val < 633 then 632 else 633) else (if
      i.val < 635 then 634 else 635))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 636 else (if i.val < 638 then 637 else 638)) else
      (if i.val < 640 then 639 else (if i.val < 641 then 640 else 641))) else (if i.val < 645
      then (if i.val < 643 then 642 else (if i.val < 644 then 643 else 644)) else (if i.val <
      647 then (if i.val < 646 then 645 else 646) else (if i.val < 648 then 647 else 648))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 649 else (if i.val <
      651 then 650 else 651)) else (if i.val < 653 then 652 else (if i.val < 654 then 653 else
      654))) else (if i.val < 658 then (if i.val < 656 then 655 else (if i.val < 657 then 656
      else 657)) else (if i.val < 660 then (if i.val < 659 then 658 else 659) else (if i.val <
      661 then 660 else 661)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 662 else (if i.val < 664 then 663 else
      664)) else (if i.val < 666 then 665 else (if i.val < 667 then 666 else 667))) else (if
      i.val < 671 then (if i.val < 669 then 668 else (if i.val < 670 then 669 else 670)) else
      (if i.val < 672 then 671 else (if i.val < 673 then 672 else 673)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 674 else (if i.val < 676 then 675 else
      676)) else (if i.val < 678 then 677 else (if i.val < 679 then 678 else 679))) else (if
      i.val < 683 then (if i.val < 681 then 680 else (if i.val < 682 then 681 else 682)) else
      (if i.val < 685 then (if i.val < 684 then 683 else 684) else (if i.val < 686 then 685 else
      686))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 687 else (if i.val < 689 then 688 else 689)) else (if i.val < 691 then 690 else
      (if i.val < 692 then 691 else 692))) else (if i.val < 696 then (if i.val < 694 then 693
      else (if i.val < 695 then 694 else 695)) else (if i.val < 698 then (if i.val < 697 then
      696 else 697) else (if i.val < 699 then 698 else 699)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 700 else (if i.val < 702 then 701 else 702)) else
      (if i.val < 704 then 703 else (if i.val < 705 then 704 else 705))) else (if i.val < 709
      then (if i.val < 707 then 706 else (if i.val < 708 then 707 else 708)) else (if i.val <
      711 then (if i.val < 710 then 709 else 710) else (if i.val < 712 then 711 else 712)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 713 else (if i.val < 715 then 714 else 715))
      else (if i.val < 717 then 716 else (if i.val < 718 then 717 else 718))) else (if i.val <
      722 then (if i.val < 720 then 719 else (if i.val < 721 then 720 else 721)) else (if i.val
      < 723 then 722 else (if i.val < 724 then 723 else 724)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 725 else (if i.val < 727 then 726 else 727)) else
      (if i.val < 729 then 728 else (if i.val < 730 then 729 else 730))) else (if i.val < 734
      then (if i.val < 732 then 731 else (if i.val < 733 then 732 else 733)) else (if i.val <
      736 then (if i.val < 735 then 734 else 735) else (if i.val < 737 then 736 else 737)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      738 else (if i.val < 740 then 739 else 740)) else (if i.val < 742 then 741 else (if i.val
      < 743 then 742 else 743))) else (if i.val < 747 then (if i.val < 745 then 744 else (if
      i.val < 746 then 745 else 746)) else (if i.val < 749 then (if i.val < 748 then 747 else
      748) else (if i.val < 750 then 749 else 750)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 751 else (if i.val < 753 then 752 else 753)) else (if i.val <
      755 then 754 else (if i.val < 756 then 755 else 756))) else (if i.val < 760 then (if i.val
      < 758 then 757 else (if i.val < 759 then 758 else 759)) else (if i.val < 762 then (if
      i.val < 761 then 760 else 761) else (if i.val < 763 then 762 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 771 else 772)) else (if i.val < 774 then 773 else (if i.val < 775
      then 774 else 775)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      776 else (if i.val < 778 then 777 else 778)) else (if i.val < 780 then 779 else (if i.val
      < 781 then 780 else 781))) else (if i.val < 785 then (if i.val < 783 then 782 else (if
      i.val < 784 then 783 else 784)) else (if i.val < 787 then (if i.val < 786 then 785 else
      786) else (if i.val < 788 then 787 else 788))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 789 else (if i.val < 791 then 790 else
      791)) else (if i.val < 793 then 792 else (if i.val < 794 then 793 else 794))) else (if
      i.val < 798 then (if i.val < 796 then 795 else (if i.val < 797 then 796 else 797)) else
      (if i.val < 800 then (if i.val < 799 then 798 else 799) else (if i.val < 801 then 800 else
      801)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 802 else (if
      i.val < 804 then 803 else 804)) else (if i.val < 806 then 805 else (if i.val < 807 then
      806 else 807))) else (if i.val < 811 then (if i.val < 809 then 808 else (if i.val < 810
      then 809 else 810)) else (if i.val < 813 then (if i.val < 812 then 811 else 812) else (if
      i.val < 814 then 813 else 814)))))))))))
  invFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 0 else (if i.val < 2 then 1 else 2)) else (if i.val < 4 then 3 else (if i.val < 5
      then 4 else 5))) else (if i.val < 9 then (if i.val < 7 then 6 else (if i.val < 8 then 7
      else 8)) else (if i.val < 10 then 9 else (if i.val < 11 then 10 else 11)))) else (if i.val
      < 18 then (if i.val < 15 then (if i.val < 13 then 12 else (if i.val < 14 then 13 else 14))
      else (if i.val < 16 then 15 else (if i.val < 17 then 16 else 17))) else (if i.val < 21
      then (if i.val < 19 then 18 else (if i.val < 20 then 19 else 20)) else (if i.val < 23 then
      (if i.val < 22 then 21 else 22) else (if i.val < 24 then 23 else 24))))) else (if i.val <
      37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 25 else (if i.val < 27
      then 26 else 27)) else (if i.val < 29 then 28 else (if i.val < 30 then 29 else 30))) else
      (if i.val < 34 then (if i.val < 32 then 31 else (if i.val < 33 then 32 else 33)) else (if
      i.val < 35 then 34 else (if i.val < 36 then 35 else 36)))) else (if i.val < 43 then (if
      i.val < 40 then (if i.val < 38 then 37 else (if i.val < 39 then 38 else 39)) else (if
      i.val < 41 then 40 else (if i.val < 42 then 41 else 42))) else (if i.val < 46 then (if
      i.val < 44 then 43 else (if i.val < 45 then 44 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 46 else 47) else (if i.val < 49 then 48 else 49)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 50
      else (if i.val < 52 then 51 else 52)) else (if i.val < 54 then 53 else (if i.val < 55 then
      54 else 55))) else (if i.val < 59 then (if i.val < 57 then 56 else (if i.val < 58 then 57
      else 58)) else (if i.val < 60 then 59 else (if i.val < 61 then 60 else 61)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 62 else (if i.val < 64 then 63
      else 64)) else (if i.val < 66 then 65 else (if i.val < 67 then 66 else 67))) else (if
      i.val < 71 then (if i.val < 69 then 68 else (if i.val < 70 then 69 else 70)) else (if
      i.val < 73 then (if i.val < 72 then 71 else 72) else (if i.val < 74 then 73 else 74)))))
      else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then 75
      else (if i.val < 77 then 76 else 77)) else (if i.val < 79 then 78 else (if i.val < 80 then
      79 else 80))) else (if i.val < 84 then (if i.val < 82 then 81 else (if i.val < 83 then 82
      else 83)) else (if i.val < 86 then (if i.val < 85 then 84 else 85) else (if i.val < 87
      then 86 else 87)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then 88
      else (if i.val < 90 then 89 else 90)) else (if i.val < 92 then 91 else (if i.val < 93 then
      92 else 93))) else (if i.val < 97 then (if i.val < 95 then 94 else (if i.val < 96 then 95
      else 96)) else (if i.val < 99 then (if i.val < 98 then 97 else 98) else (if i.val < 100
      then 99 else 100))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113
      then (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 101 else (if i.val <
      103 then 102 else 103)) else (if i.val < 105 then 104 else (if i.val < 106 then 105 else
      106))) else (if i.val < 110 then (if i.val < 108 then 107 else (if i.val < 109 then 108
      else 109)) else (if i.val < 111 then 110 else (if i.val < 112 then 111 else 112)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 113 else (if i.val < 115
      then 114 else 115)) else (if i.val < 117 then 116 else (if i.val < 118 then 117 else
      118))) else (if i.val < 122 then (if i.val < 120 then 119 else (if i.val < 121 then 120
      else 121)) else (if i.val < 124 then (if i.val < 123 then 122 else 123) else (if i.val <
      125 then 124 else 125))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 126 else (if i.val < 128 then 127 else 128)) else (if i.val <
      130 then 129 else (if i.val < 131 then 130 else 131))) else (if i.val < 135 then (if i.val
      < 133 then 132 else (if i.val < 134 then 133 else 134)) else (if i.val < 137 then (if
      i.val < 136 then 135 else 136) else (if i.val < 138 then 137 else 138)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 139 else (if i.val < 141 then 140 else
      141)) else (if i.val < 143 then 142 else (if i.val < 144 then 143 else 144))) else (if
      i.val < 148 then (if i.val < 146 then 145 else (if i.val < 147 then 146 else 147)) else
      (if i.val < 150 then (if i.val < 149 then 148 else 149) else (if i.val < 151 then 150 else
      151)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 152 else (if i.val < 154 then 153 else 154)) else (if i.val
      < 156 then 155 else (if i.val < 157 then 156 else 157))) else (if i.val < 161 then (if
      i.val < 159 then 158 else (if i.val < 160 then 159 else 160)) else (if i.val < 162 then
      161 else (if i.val < 163 then 162 else 163)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 164 else (if i.val < 166 then 165 else 166)) else (if i.val <
      168 then 167 else (if i.val < 169 then 168 else 169))) else (if i.val < 173 then (if i.val
      < 171 then 170 else (if i.val < 172 then 171 else 172)) else (if i.val < 175 then (if
      i.val < 174 then 173 else 174) else (if i.val < 176 then 175 else 176))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 177 else (if
      i.val < 179 then 178 else 179)) else (if i.val < 181 then 180 else (if i.val < 182 then
      181 else 182))) else (if i.val < 186 then (if i.val < 184 then 183 else (if i.val < 185
      then 184 else 185)) else (if i.val < 188 then (if i.val < 187 then 186 else 187) else (if
      i.val < 189 then 188 else 189)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 190 else (if i.val < 192 then 191 else 192)) else (if i.val < 194 then 193 else
      (if i.val < 195 then 194 else 195))) else (if i.val < 199 then (if i.val < 197 then 196
      else (if i.val < 198 then 197 else 198)) else (if i.val < 201 then (if i.val < 200 then
      199 else 200) else (if i.val < 202 then 201 else 202)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 203 else (if i.val < 205 then 204 else 205)) else (if
      i.val < 207 then 206 else (if i.val < 208 then 207 else 208))) else (if i.val < 212 then
      (if i.val < 210 then 209 else (if i.val < 211 then 210 else 211)) else (if i.val < 213
      then 212 else (if i.val < 214 then 213 else 214)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 215 else (if i.val < 217 then 216 else 217)) else (if i.val
      < 219 then 218 else (if i.val < 220 then 219 else 220))) else (if i.val < 224 then (if
      i.val < 222 then 221 else (if i.val < 223 then 222 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 226 else 227))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 228 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 233))) else (if i.val < 237 then (if i.val < 235 then 234 else (if i.val <
      236 then 235 else 236)) else (if i.val < 239 then (if i.val < 238 then 237 else 238) else
      (if i.val < 240 then 239 else 240)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 241 else (if i.val < 243 then 242 else 243)) else (if i.val < 245 then
      244 else (if i.val < 246 then 245 else 246))) else (if i.val < 250 then (if i.val < 248
      then 247 else (if i.val < 249 then 248 else 249)) else (if i.val < 252 then (if i.val <
      251 then 250 else 251) else (if i.val < 253 then 252 else 253)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      254 else (if i.val < 256 then 255 else 256)) else (if i.val < 258 then 257 else (if i.val
      < 259 then 258 else 259))) else (if i.val < 263 then (if i.val < 261 then 260 else (if
      i.val < 262 then 261 else 262)) else (if i.val < 264 then 263 else (if i.val < 265 then
      264 else 265)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 266
      else (if i.val < 268 then 267 else 268)) else (if i.val < 270 then 269 else (if i.val <
      271 then 270 else 271))) else (if i.val < 275 then (if i.val < 273 then 272 else (if i.val
      < 274 then 273 else 274)) else (if i.val < 277 then (if i.val < 276 then 275 else 276)
      else (if i.val < 278 then 277 else 278))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 279 else (if i.val < 281 then 280 else 281))
      else (if i.val < 283 then 282 else (if i.val < 284 then 283 else 284))) else (if i.val <
      288 then (if i.val < 286 then 285 else (if i.val < 287 then 286 else 287)) else (if i.val
      < 290 then (if i.val < 289 then 288 else 289) else (if i.val < 291 then 290 else 291))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 292 else (if i.val <
      294 then 293 else 294)) else (if i.val < 296 then 295 else (if i.val < 297 then 296 else
      297))) else (if i.val < 301 then (if i.val < 299 then 298 else (if i.val < 300 then 299
      else 300)) else (if i.val < 303 then (if i.val < 302 then 301 else 302) else (if i.val <
      304 then 303 else 304))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 305 else (if i.val
      < 307 then 306 else 307)) else (if i.val < 309 then 308 else (if i.val < 310 then 309 else
      310))) else (if i.val < 314 then (if i.val < 312 then 311 else (if i.val < 313 then 312
      else 313)) else (if i.val < 315 then 314 else (if i.val < 316 then 315 else 316)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 317 else (if i.val < 319
      then 318 else 319)) else (if i.val < 321 then 320 else (if i.val < 322 then 321 else
      322))) else (if i.val < 326 then (if i.val < 324 then 323 else (if i.val < 325 then 324
      else 325)) else (if i.val < 328 then (if i.val < 327 then 326 else 327) else (if i.val <
      329 then 328 else 329))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 330 else (if i.val < 332 then 331 else 332)) else (if i.val <
      334 then 333 else (if i.val < 335 then 334 else 335))) else (if i.val < 339 then (if i.val
      < 337 then 336 else (if i.val < 338 then 337 else 338)) else (if i.val < 341 then (if
      i.val < 340 then 339 else 340) else (if i.val < 342 then 341 else 342)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 343 else (if i.val < 345 then 344 else
      345)) else (if i.val < 347 then 346 else (if i.val < 348 then 347 else 348))) else (if
      i.val < 352 then (if i.val < 350 then 349 else (if i.val < 351 then 350 else 351)) else
      (if i.val < 354 then (if i.val < 353 then 352 else 353) else (if i.val < 355 then 354 else
      355)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 356 else (if i.val < 358 then 357 else 358)) else (if i.val
      < 360 then 359 else (if i.val < 361 then 360 else 361))) else (if i.val < 365 then (if
      i.val < 363 then 362 else (if i.val < 364 then 363 else 364)) else (if i.val < 366 then
      365 else (if i.val < 367 then 366 else 367)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 368 else (if i.val < 370 then 369 else 370)) else (if i.val <
      372 then 371 else (if i.val < 373 then 372 else 373))) else (if i.val < 377 then (if i.val
      < 375 then 374 else (if i.val < 376 then 375 else 376)) else (if i.val < 379 then (if
      i.val < 378 then 377 else 378) else (if i.val < 380 then 379 else 380))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 381 else (if
      i.val < 383 then 382 else 383)) else (if i.val < 385 then 384 else (if i.val < 386 then
      385 else 386))) else (if i.val < 390 then (if i.val < 388 then 387 else (if i.val < 389
      then 388 else 389)) else (if i.val < 392 then (if i.val < 391 then 390 else 391) else (if
      i.val < 393 then 392 else 393)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 394 else (if i.val < 396 then 395 else 396)) else (if i.val < 398 then 397 else
      (if i.val < 399 then 398 else 399))) else (if i.val < 403 then (if i.val < 401 then 400
      else (if i.val < 402 then 401 else 402)) else (if i.val < 405 then (if i.val < 404 then
      403 else 404) else (if i.val < 406 then 405 else 406))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 407 else (if i.val < 409 then
      408 else 409)) else (if i.val < 411 then 410 else (if i.val < 412 then 411 else 412)))
      else (if i.val < 416 then (if i.val < 414 then 413 else (if i.val < 415 then 414 else
      415)) else (if i.val < 417 then 416 else (if i.val < 418 then 417 else 418)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 419 else (if i.val < 421 then
      420 else 421)) else (if i.val < 423 then 422 else (if i.val < 424 then 423 else 424)))
      else (if i.val < 428 then (if i.val < 426 then 425 else (if i.val < 427 then 426 else
      427)) else (if i.val < 430 then (if i.val < 429 then 428 else 429) else (if i.val < 431
      then 430 else 431))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 432 else (if i.val < 434 then 433 else 434)) else (if i.val < 436
      then 435 else (if i.val < 437 then 436 else 437))) else (if i.val < 441 then (if i.val <
      439 then 438 else (if i.val < 440 then 439 else 440)) else (if i.val < 443 then (if i.val
      < 442 then 441 else 442) else (if i.val < 444 then 443 else 444)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 445 else (if i.val < 447 then 446 else
      447)) else (if i.val < 449 then 448 else (if i.val < 450 then 449 else 450))) else (if
      i.val < 454 then (if i.val < 452 then 451 else (if i.val < 453 then 452 else 453)) else
      (if i.val < 456 then (if i.val < 455 then 454 else 455) else (if i.val < 457 then 456 else
      457)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 458 else (if i.val < 460 then 459 else 460)) else (if i.val
      < 462 then 461 else (if i.val < 463 then 462 else 463))) else (if i.val < 467 then (if
      i.val < 465 then 464 else (if i.val < 466 then 465 else 466)) else (if i.val < 468 then
      467 else (if i.val < 469 then 468 else 469)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 473 else (if i.val < 475 then 474 else 475))) else (if i.val < 479 then (if i.val
      < 477 then 476 else (if i.val < 478 then 477 else 478)) else (if i.val < 481 then (if
      i.val < 480 then 479 else 480) else (if i.val < 482 then 481 else 482))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 483 else (if
      i.val < 485 then 484 else 485)) else (if i.val < 487 then 486 else (if i.val < 488 then
      487 else 488))) else (if i.val < 492 then (if i.val < 490 then 489 else (if i.val < 491
      then 490 else 491)) else (if i.val < 494 then (if i.val < 493 then 492 else 493) else (if
      i.val < 495 then 494 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 496 else (if i.val < 498 then 497 else 498)) else (if i.val < 500 then 499 else
      (if i.val < 501 then 500 else 501))) else (if i.val < 505 then (if i.val < 503 then 502
      else (if i.val < 504 then 503 else 504)) else (if i.val < 507 then (if i.val < 506 then
      505 else 506) else (if i.val < 508 then 507 else 508))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 509 else (if i.val < 511 then 510 else 511)) else (if i.val < 513 then 512 else
      (if i.val < 514 then 513 else 514))) else (if i.val < 518 then (if i.val < 516 then 515
      else (if i.val < 517 then 516 else 517)) else (if i.val < 519 then 518 else (if i.val <
      520 then 519 else 520)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 521 else (if i.val < 523 then 522 else 523)) else (if i.val < 525 then 524 else (if
      i.val < 526 then 525 else 526))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 529)) else (if i.val < 532 then (if i.val < 531 then 530
      else 531) else (if i.val < 533 then 532 else 533))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 534 else (if i.val < 536 then 535
      else 536)) else (if i.val < 538 then 537 else (if i.val < 539 then 538 else 539))) else
      (if i.val < 543 then (if i.val < 541 then 540 else (if i.val < 542 then 541 else 542))
      else (if i.val < 545 then (if i.val < 544 then 543 else 544) else (if i.val < 546 then 545
      else 546)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 547 else
      (if i.val < 549 then 548 else 549)) else (if i.val < 551 then 550 else (if i.val < 552
      then 551 else 552))) else (if i.val < 556 then (if i.val < 554 then 553 else (if i.val <
      555 then 554 else 555)) else (if i.val < 558 then (if i.val < 557 then 556 else 557) else
      (if i.val < 559 then 558 else 559)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 560 else (if i.val < 562 then
      561 else 562)) else (if i.val < 564 then 563 else (if i.val < 565 then 564 else 565)))
      else (if i.val < 569 then (if i.val < 567 then 566 else (if i.val < 568 then 567 else
      568)) else (if i.val < 570 then 569 else (if i.val < 571 then 570 else 571)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 572 else (if i.val < 574 then
      573 else 574)) else (if i.val < 576 then 575 else (if i.val < 577 then 576 else 577)))
      else (if i.val < 581 then (if i.val < 579 then 578 else (if i.val < 580 then 579 else
      580)) else (if i.val < 583 then (if i.val < 582 then 581 else 582) else (if i.val < 584
      then 583 else 584))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 585 else (if i.val < 587 then 586 else 587)) else (if i.val < 589
      then 588 else (if i.val < 590 then 589 else 590))) else (if i.val < 594 then (if i.val <
      592 then 591 else (if i.val < 593 then 592 else 593)) else (if i.val < 596 then (if i.val
      < 595 then 594 else 595) else (if i.val < 597 then 596 else 597)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 598 else (if i.val < 600 then 599 else
      600)) else (if i.val < 602 then 601 else (if i.val < 603 then 602 else 603))) else (if
      i.val < 607 then (if i.val < 605 then 604 else (if i.val < 606 then 605 else 606)) else
      (if i.val < 609 then (if i.val < 608 then 607 else 608) else (if i.val < 610 then 609 else
      610)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 611 else (if
      i.val < 613 then 612 else 613)) else (if i.val < 615 then 614 else (if i.val < 616 then
      615 else 616))) else (if i.val < 620 then (if i.val < 618 then 617 else (if i.val < 619
      then 618 else 619)) else (if i.val < 621 then 620 else (if i.val < 622 then 621 else
      622)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 623 else (if
      i.val < 625 then 624 else 625)) else (if i.val < 627 then 626 else (if i.val < 628 then
      627 else 628))) else (if i.val < 632 then (if i.val < 630 then 629 else (if i.val < 631
      then 630 else 631)) else (if i.val < 634 then (if i.val < 633 then 632 else 633) else (if
      i.val < 635 then 634 else 635))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 636 else (if i.val < 638 then 637 else 638)) else
      (if i.val < 640 then 639 else (if i.val < 641 then 640 else 641))) else (if i.val < 645
      then (if i.val < 643 then 642 else (if i.val < 644 then 643 else 644)) else (if i.val <
      647 then (if i.val < 646 then 645 else 646) else (if i.val < 648 then 647 else 648))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 649 else (if i.val <
      651 then 650 else 651)) else (if i.val < 653 then 652 else (if i.val < 654 then 653 else
      654))) else (if i.val < 658 then (if i.val < 656 then 655 else (if i.val < 657 then 656
      else 657)) else (if i.val < 660 then (if i.val < 659 then 658 else 659) else (if i.val <
      661 then 660 else 661)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 662 else (if i.val < 664 then 663 else
      664)) else (if i.val < 666 then 665 else (if i.val < 667 then 666 else 667))) else (if
      i.val < 671 then (if i.val < 669 then 668 else (if i.val < 670 then 669 else 670)) else
      (if i.val < 672 then 671 else (if i.val < 673 then 672 else 673)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 674 else (if i.val < 676 then 675 else
      676)) else (if i.val < 678 then 677 else (if i.val < 679 then 678 else 679))) else (if
      i.val < 683 then (if i.val < 681 then 680 else (if i.val < 682 then 681 else 682)) else
      (if i.val < 685 then (if i.val < 684 then 683 else 684) else (if i.val < 686 then 685 else
      686))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 687 else (if i.val < 689 then 688 else 689)) else (if i.val < 691 then 690 else
      (if i.val < 692 then 691 else 692))) else (if i.val < 696 then (if i.val < 694 then 693
      else (if i.val < 695 then 694 else 695)) else (if i.val < 698 then (if i.val < 697 then
      696 else 697) else (if i.val < 699 then 698 else 699)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 700 else (if i.val < 702 then 701 else 702)) else
      (if i.val < 704 then 703 else (if i.val < 705 then 704 else 705))) else (if i.val < 709
      then (if i.val < 707 then 706 else (if i.val < 708 then 707 else 708)) else (if i.val <
      711 then (if i.val < 710 then 709 else 710) else (if i.val < 712 then 711 else 712)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 713 else (if i.val < 715 then 714 else 715))
      else (if i.val < 717 then 716 else (if i.val < 718 then 717 else 718))) else (if i.val <
      722 then (if i.val < 720 then 719 else (if i.val < 721 then 720 else 721)) else (if i.val
      < 723 then 722 else (if i.val < 724 then 723 else 724)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 725 else (if i.val < 727 then 726 else 727)) else
      (if i.val < 729 then 728 else (if i.val < 730 then 729 else 730))) else (if i.val < 734
      then (if i.val < 732 then 731 else (if i.val < 733 then 732 else 733)) else (if i.val <
      736 then (if i.val < 735 then 734 else 735) else (if i.val < 737 then 736 else 737)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      738 else (if i.val < 740 then 739 else 740)) else (if i.val < 742 then 741 else (if i.val
      < 743 then 742 else 743))) else (if i.val < 747 then (if i.val < 745 then 744 else (if
      i.val < 746 then 745 else 746)) else (if i.val < 749 then (if i.val < 748 then 747 else
      748) else (if i.val < 750 then 749 else 750)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 751 else (if i.val < 753 then 752 else 753)) else (if i.val <
      755 then 754 else (if i.val < 756 then 755 else 756))) else (if i.val < 760 then (if i.val
      < 758 then 757 else (if i.val < 759 then 758 else 759)) else (if i.val < 762 then (if
      i.val < 761 then 760 else 761) else (if i.val < 763 then 762 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 771 else 772)) else (if i.val < 774 then 773 else (if i.val < 775
      then 774 else 775)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      776 else (if i.val < 778 then 777 else 778)) else (if i.val < 780 then 779 else (if i.val
      < 781 then 780 else 781))) else (if i.val < 785 then (if i.val < 783 then 782 else (if
      i.val < 784 then 783 else 784)) else (if i.val < 787 then (if i.val < 786 then 785 else
      786) else (if i.val < 788 then 787 else 788))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 789 else (if i.val < 791 then 790 else
      791)) else (if i.val < 793 then 792 else (if i.val < 794 then 793 else 794))) else (if
      i.val < 798 then (if i.val < 796 then 795 else (if i.val < 797 then 796 else 797)) else
      (if i.val < 800 then (if i.val < 799 then 798 else 799) else (if i.val < 801 then 800 else
      801)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 802 else (if
      i.val < 804 then 803 else 804)) else (if i.val < 806 then 805 else (if i.val < 807 then
      806 else 807))) else (if i.val < 811 then (if i.val < 809 then 808 else (if i.val < 810
      then 809 else 810)) else (if i.val < 813 then (if i.val < 812 then 811 else 812) else (if
      i.val < 814 then 813 else 814)))))))))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed vertex, edge and branch bijections for this frame permutation. -/
def hint0 : Fin 815 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
    (if i.val < 25 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 37 then ⟨[0, 1], [0], [false]⟩
    else (if i.val < 43 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 46 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 48 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else (if i.val < 105 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val
    < 106 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩))) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 119 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 122 then (if i.val < 120
    then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 121 then ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else ⟨[0,
    1, 2], [0, 1], [false, false]⟩))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2],
    [0, 1], [false, false]⟩)) else (if i.val < 305 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else
    (if i.val < 356 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 381 then (if i.val
    < 368 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 374 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else (if i.val < 377 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 1,
    2, 3], [0, 1, 2], [false, false, false]⟩))) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩)))) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 483 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 496 then (if i.val < 489 then ⟨[0, 1, 2, 3], [0, 1,
    2], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else (if i.val < 502
    then (if i.val < 499 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 1], [0, 1], [false,
    false]⟩) else ⟨[0, 1], [0, 1], [false, false]⟩)))) else ⟨[0, 1], [0, 1], [false, false]⟩)
    else (if i.val < 713 then (if i.val < 662 then ⟨[0, 1], [0, 1], [false, false]⟩ else ⟨[0, 1,
    2], [0, 1, 2], [false, false, false]⟩) else (if i.val < 764 then ⟨[0, 1, 2], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 789 then ⟨[0, 1, 2], [0, 1, 2], [false, false,
    false]⟩ else (if i.val < 802 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if
    i.val < 808 then (if i.val < 805 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else
    ⟨[0, 1], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1], [0, 1, 2], [false, false,
    false]⟩))))))))

/-- The kernel checks the supplied bijections without repeating permutation search. -/
theorem hints_valid0 : ∀ i, (hint0 i).check ((L24Graphs.graph i).relabel labels0)
    (L24Graphs.graph (destination0 i)) = true := by
  decide +kernel

/-- Every column is transported as a full decorated labelled graph. -/
theorem covered0 : ∀ i, ((L24Graphs.graph i).relabel labels0).isomorphic?
    (L24Graphs.graph (destination0 i)) = true := by
  intro i
  exact (hint0 i).check_sound _ _ (hints_valid0 i)

/-- The 1-th permutation of the three free markings; old labels map covariantly. -/
def labels1 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 3, 2]
  invFun := ![0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A candidate bijection of the held frame columns. -/
def destination1 : Equiv.Perm (Fin 815) where
  toFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 0 else (if i.val < 2 then 1 else 2)) else (if i.val < 4 then 3 else (if i.val < 5
      then 7 else 8))) else (if i.val < 9 then (if i.val < 7 then 9 else (if i.val < 8 then 4
      else 5)) else (if i.val < 10 then 6 else (if i.val < 11 then 10 else 12)))) else (if i.val
      < 18 then (if i.val < 15 then (if i.val < 13 then 11 else (if i.val < 14 then 13 else 14))
      else (if i.val < 16 then 19 else (if i.val < 17 then 20 else 21))) else (if i.val < 21
      then (if i.val < 19 then 22 else (if i.val < 20 then 15 else 16)) else (if i.val < 23 then
      (if i.val < 22 then 17 else 18) else (if i.val < 24 then 23 else 24))))) else (if i.val <
      37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 27 else (if i.val < 27
      then 28 else 25)) else (if i.val < 29 then 26 else (if i.val < 30 then 29 else 30))) else
      (if i.val < 34 then (if i.val < 32 then 33 else (if i.val < 33 then 32 else 31)) else (if
      i.val < 35 then 39 else (if i.val < 36 then 40 else 41)))) else (if i.val < 43 then (if
      i.val < 40 then (if i.val < 38 then 42 else (if i.val < 39 then 43 else 34)) else (if
      i.val < 41 then 35 else (if i.val < 42 then 36 else 37))) else (if i.val < 46 then (if
      i.val < 44 then 38 else (if i.val < 45 then 44 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 47 else 46) else (if i.val < 49 then 48 else 49)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 50
      else (if i.val < 52 then 51 else 52)) else (if i.val < 54 then 53 else (if i.val < 55 then
      54 else 55))) else (if i.val < 59 then (if i.val < 57 then 56 else (if i.val < 58 then 64
      else 65)) else (if i.val < 60 then 66 else (if i.val < 61 then 67 else 68)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 69 else (if i.val < 64 then 70
      else 57)) else (if i.val < 66 then 58 else (if i.val < 67 then 59 else 60))) else (if
      i.val < 71 then (if i.val < 69 then 61 else (if i.val < 70 then 62 else 63)) else (if
      i.val < 73 then (if i.val < 72 then 71 else 73) else (if i.val < 74 then 72 else 74)))))
      else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then 82
      else (if i.val < 77 then 83 else 84)) else (if i.val < 79 then 85 else (if i.val < 80 then
      86 else 87))) else (if i.val < 84 then (if i.val < 82 then 88 else (if i.val < 83 then 75
      else 76)) else (if i.val < 86 then (if i.val < 85 then 77 else 78) else (if i.val < 87
      then 79 else 80)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then 81
      else (if i.val < 90 then 89 else 91)) else (if i.val < 92 then 90 else (if i.val < 93 then
      92 else 95))) else (if i.val < 97 then (if i.val < 95 then 96 else (if i.val < 96 then 93
      else 94)) else (if i.val < 99 then (if i.val < 98 then 97 else 102) else (if i.val < 100
      then 103 else 104))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113
      then (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 105 else (if i.val <
      103 then 98 else 99)) else (if i.val < 105 then 100 else (if i.val < 106 then 101 else
      106))) else (if i.val < 110 then (if i.val < 108 then 107 else (if i.val < 109 then 108
      else 112)) else (if i.val < 111 then 113 else (if i.val < 112 then 114 else 109)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 110 else (if i.val < 115
      then 111 else 117)) else (if i.val < 117 then 118 else (if i.val < 118 then 115 else
      116))) else (if i.val < 122 then (if i.val < 120 then 120 else (if i.val < 121 then 119
      else 121)) else (if i.val < 124 then (if i.val < 123 then 122 else 123) else (if i.val <
      125 then 124 else 125))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 126 else (if i.val < 128 then 127 else 128)) else (if i.val <
      130 then 129 else (if i.val < 131 then 130 else 131))) else (if i.val < 135 then (if i.val
      < 133 then 132 else (if i.val < 134 then 133 else 134)) else (if i.val < 137 then (if
      i.val < 136 then 135 else 136) else (if i.val < 138 then 137 else 138)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 139 else (if i.val < 141 then 155 else
      156)) else (if i.val < 143 then 157 else (if i.val < 144 then 158 else 159))) else (if
      i.val < 148 then (if i.val < 146 then 160 else (if i.val < 147 then 161 else 162)) else
      (if i.val < 150 then (if i.val < 149 then 163 else 164) else (if i.val < 151 then 165 else
      166)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 167 else (if i.val < 154 then 168 else 169)) else (if i.val
      < 156 then 140 else (if i.val < 157 then 141 else 142))) else (if i.val < 161 then (if
      i.val < 159 then 143 else (if i.val < 160 then 144 else 145)) else (if i.val < 162 then
      146 else (if i.val < 163 then 147 else 148)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 149 else (if i.val < 166 then 150 else 151)) else (if i.val <
      168 then 152 else (if i.val < 169 then 153 else 154))) else (if i.val < 173 then (if i.val
      < 171 then 170 else (if i.val < 172 then 172 else 171)) else (if i.val < 175 then (if
      i.val < 174 then 173 else 174) else (if i.val < 176 then 175 else 177))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 176 else (if
      i.val < 179 then 178 else 179)) else (if i.val < 181 then 180 else (if i.val < 182 then
      181 else 201))) else (if i.val < 186 then (if i.val < 184 then 202 else (if i.val < 185
      then 203 else 204)) else (if i.val < 188 then (if i.val < 187 then 205 else 206) else (if
      i.val < 189 then 207 else 208)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 209 else (if i.val < 192 then 210 else 211)) else (if i.val < 194 then 212 else
      (if i.val < 195 then 213 else 214))) else (if i.val < 199 then (if i.val < 197 then 215
      else (if i.val < 198 then 216 else 217)) else (if i.val < 201 then (if i.val < 200 then
      218 else 219) else (if i.val < 202 then 182 else 183)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 184 else (if i.val < 205 then 185 else 186)) else (if
      i.val < 207 then 187 else (if i.val < 208 then 188 else 189))) else (if i.val < 212 then
      (if i.val < 210 then 190 else (if i.val < 211 then 191 else 192)) else (if i.val < 213
      then 193 else (if i.val < 214 then 194 else 195)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 196 else (if i.val < 217 then 197 else 198)) else (if i.val
      < 219 then 199 else (if i.val < 220 then 200 else 220))) else (if i.val < 224 then (if
      i.val < 222 then 222 else (if i.val < 223 then 221 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 226 else 228))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 227 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 234))) else (if i.val < 237 then (if i.val < 235 then 233 else (if i.val <
      236 then 235 else 236)) else (if i.val < 239 then (if i.val < 238 then 238 else 237) else
      (if i.val < 240 then 239 else 246)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 247 else (if i.val < 243 then 244 else 245)) else (if i.val < 245 then
      242 else (if i.val < 246 then 243 else 240))) else (if i.val < 250 then (if i.val < 248
      then 241 else (if i.val < 249 then 260 else 261)) else (if i.val < 252 then (if i.val <
      251 then 262 else 263) else (if i.val < 253 then 264 else 265)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      266 else (if i.val < 256 then 267 else 268)) else (if i.val < 258 then 269 else (if i.val
      < 259 then 270 else 271))) else (if i.val < 263 then (if i.val < 261 then 248 else (if
      i.val < 262 then 249 else 250)) else (if i.val < 264 then 251 else (if i.val < 265 then
      252 else 253)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 254
      else (if i.val < 268 then 255 else 256)) else (if i.val < 270 then 257 else (if i.val <
      271 then 258 else 259))) else (if i.val < 275 then (if i.val < 273 then 272 else (if i.val
      < 274 then 273 else 275)) else (if i.val < 277 then (if i.val < 276 then 274 else 277)
      else (if i.val < 278 then 276 else 279))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 278 else (if i.val < 281 then 280 else 281))
      else (if i.val < 283 then 282 else (if i.val < 284 then 284 else 283))) else (if i.val <
      288 then (if i.val < 286 then 288 else (if i.val < 287 then 289 else 290)) else (if i.val
      < 290 then (if i.val < 289 then 285 else 286) else (if i.val < 291 then 287 else 291))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 293 else (if i.val <
      294 then 292 else 294)) else (if i.val < 296 then 295 else (if i.val < 297 then 300 else
      301))) else (if i.val < 301 then (if i.val < 299 then 302 else (if i.val < 300 then 303
      else 296)) else (if i.val < 303 then (if i.val < 302 then 297 else 298) else (if i.val <
      304 then 299 else 304))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 306 else (if i.val
      < 307 then 305 else 307)) else (if i.val < 309 then 308 else (if i.val < 310 then 310 else
      309))) else (if i.val < 314 then (if i.val < 312 then 315 else (if i.val < 313 then 316
      else 317)) else (if i.val < 315 then 318 else (if i.val < 316 then 311 else 312)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 313 else (if i.val < 319
      then 314 else 319)) else (if i.val < 321 then 320 else (if i.val < 322 then 322 else
      321))) else (if i.val < 326 then (if i.val < 324 then 344 else (if i.val < 325 then 345
      else 346)) else (if i.val < 328 then (if i.val < 327 then 347 else 348) else (if i.val <
      329 then 349 else 350))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 351 else (if i.val < 332 then 352 else 353)) else (if i.val <
      334 then 354 else (if i.val < 335 then 355 else 356))) else (if i.val < 339 then (if i.val
      < 337 then 357 else (if i.val < 338 then 358 else 359)) else (if i.val < 341 then (if
      i.val < 340 then 360 else 343) else (if i.val < 342 then 341 else 342)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 340 else (if i.val < 345 then 323 else
      324)) else (if i.val < 347 then 325 else (if i.val < 348 then 326 else 327))) else (if
      i.val < 352 then (if i.val < 350 then 328 else (if i.val < 351 then 329 else 330)) else
      (if i.val < 354 then (if i.val < 353 then 331 else 332) else (if i.val < 355 then 333 else
      334)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 335 else (if i.val < 358 then 336 else 337)) else (if i.val
      < 360 then 338 else (if i.val < 361 then 339 else 362))) else (if i.val < 365 then (if
      i.val < 363 then 361 else (if i.val < 364 then 363 else 364)) else (if i.val < 366 then
      366 else (if i.val < 367 then 365 else 367)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 369 else (if i.val < 370 then 368 else 370)) else (if i.val <
      372 then 374 else (if i.val < 373 then 375 else 376))) else (if i.val < 377 then (if i.val
      < 375 then 371 else (if i.val < 376 then 372 else 373)) else (if i.val < 379 then (if
      i.val < 378 then 377 else 378) else (if i.val < 380 then 379 else 380))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 381 else (if
      i.val < 383 then 382 else 383)) else (if i.val < 385 then 391 else (if i.val < 386 then
      392 else 393))) else (if i.val < 390 then (if i.val < 388 then 394 else (if i.val < 389
      then 395 else 396)) else (if i.val < 392 then (if i.val < 391 then 397 else 384) else (if
      i.val < 393 then 385 else 386)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 387 else (if i.val < 396 then 388 else 389)) else (if i.val < 398 then 390 else
      (if i.val < 399 then 398 else 404))) else (if i.val < 403 then (if i.val < 401 then 405
      else (if i.val < 402 then 406 else 407)) else (if i.val < 405 then (if i.val < 404 then
      408 else 399) else (if i.val < 406 then 400 else 401))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 402 else (if i.val < 409 then
      403 else 409)) else (if i.val < 411 then 412 else (if i.val < 412 then 413 else 410)))
      else (if i.val < 416 then (if i.val < 414 then 411 else (if i.val < 415 then 414 else
      416)) else (if i.val < 417 then 415 else (if i.val < 418 then 417 else 418)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 419 else (if i.val < 421 then
      420 else 421)) else (if i.val < 423 then 422 else (if i.val < 424 then 423 else 424)))
      else (if i.val < 428 then (if i.val < 426 then 425 else (if i.val < 427 then 426 else
      437)) else (if i.val < 430 then (if i.val < 429 then 438 else 439) else (if i.val < 431
      then 440 else 441))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 442 else (if i.val < 434 then 443 else 444)) else (if i.val < 436
      then 445 else (if i.val < 437 then 446 else 427))) else (if i.val < 441 then (if i.val <
      439 then 428 else (if i.val < 440 then 429 else 430)) else (if i.val < 443 then (if i.val
      < 442 then 431 else 432) else (if i.val < 444 then 433 else 434)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 435 else (if i.val < 447 then 436 else
      447)) else (if i.val < 449 then 448 else (if i.val < 450 then 449 else 460))) else (if
      i.val < 454 then (if i.val < 452 then 461 else (if i.val < 453 then 462 else 463)) else
      (if i.val < 456 then (if i.val < 455 then 464 else 465) else (if i.val < 457 then 466 else
      467)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 468 else (if i.val < 460 then 469 else 450)) else (if i.val
      < 462 then 451 else (if i.val < 463 then 452 else 453))) else (if i.val < 467 then (if
      i.val < 465 then 454 else (if i.val < 466 then 455 else 456)) else (if i.val < 468 then
      457 else (if i.val < 469 then 458 else 459)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 473 else (if i.val < 475 then 476 else 477))) else (if i.val < 479 then (if i.val
      < 477 then 474 else (if i.val < 478 then 475 else 478)) else (if i.val < 481 then (if
      i.val < 480 then 479 else 481) else (if i.val < 482 then 480 else 482))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 486 else (if
      i.val < 485 then 487 else 488)) else (if i.val < 487 then 483 else (if i.val < 488 then
      484 else 485))) else (if i.val < 492 then (if i.val < 490 then 489 else (if i.val < 491
      then 491 else 490)) else (if i.val < 494 then (if i.val < 493 then 492 else 494) else (if
      i.val < 495 then 493 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 496 else (if i.val < 498 then 498 else 497)) else (if i.val < 500 then 499 else
      (if i.val < 501 then 500 else 501))) else (if i.val < 505 then (if i.val < 503 then 502
      else (if i.val < 504 then 506 else 507)) else (if i.val < 507 then (if i.val < 506 then
      508 else 503) else (if i.val < 508 then 504 else 505))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 509 else (if i.val < 511 then 510 else 512)) else (if i.val < 513 then 511 else
      (if i.val < 514 then 513 else 514))) else (if i.val < 518 then (if i.val < 516 then 519
      else (if i.val < 517 then 520 else 521)) else (if i.val < 519 then 522 else (if i.val <
      520 then 515 else 516)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 517 else (if i.val < 523 then 518 else 523)) else (if i.val < 525 then 524 else (if
      i.val < 526 then 526 else 525))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 529)) else (if i.val < 532 then (if i.val < 531 then 531
      else 530) else (if i.val < 533 then 538 else 539))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 540 else (if i.val < 536 then 541
      else 542)) else (if i.val < 538 then 543 else (if i.val < 539 then 532 else 533))) else
      (if i.val < 543 then (if i.val < 541 then 534 else (if i.val < 542 then 535 else 536))
      else (if i.val < 545 then (if i.val < 544 then 537 else 544) else (if i.val < 546 then 545
      else 547)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 546 else
      (if i.val < 549 then 549 else 548)) else (if i.val < 551 then 551 else (if i.val < 552
      then 550 else 552))) else (if i.val < 556 then (if i.val < 554 then 553 else (if i.val <
      555 then 554 else 556)) else (if i.val < 558 then (if i.val < 557 then 555 else 561) else
      (if i.val < 559 then 562 else 563)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 564 else (if i.val < 562 then
      557 else 558)) else (if i.val < 564 then 559 else (if i.val < 565 then 560 else 565)))
      else (if i.val < 569 then (if i.val < 567 then 567 else (if i.val < 568 then 566 else
      568)) else (if i.val < 570 then 569 else (if i.val < 571 then 574 else 575)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 576 else (if i.val < 574 then
      577 else 570)) else (if i.val < 576 then 571 else (if i.val < 577 then 572 else 573)))
      else (if i.val < 581 then (if i.val < 579 then 578 else (if i.val < 580 then 580 else
      579)) else (if i.val < 583 then (if i.val < 582 then 581 else 582) else (if i.val < 584
      then 583 else 585))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 584 else (if i.val < 587 then 590 else 591)) else (if i.val < 589
      then 592 else (if i.val < 590 then 593 else 586))) else (if i.val < 594 then (if i.val <
      592 then 587 else (if i.val < 593 then 588 else 589)) else (if i.val < 596 then (if i.val
      < 595 then 594 else 595) else (if i.val < 597 then 597 else 596)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 598 else (if i.val < 600 then 599 else
      601)) else (if i.val < 602 then 600 else (if i.val < 603 then 606 else 607))) else (if
      i.val < 607 then (if i.val < 605 then 608 else (if i.val < 606 then 609 else 602)) else
      (if i.val < 609 then (if i.val < 608 then 603 else 604) else (if i.val < 610 then 605 else
      611)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 610 else (if
      i.val < 613 then 612 else 613)) else (if i.val < 615 then 614 else (if i.val < 616 then
      615 else 617))) else (if i.val < 620 then (if i.val < 618 then 616 else (if i.val < 619
      then 622 else 623)) else (if i.val < 621 then 624 else (if i.val < 622 then 625 else
      618)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 619 else (if
      i.val < 625 then 620 else 621)) else (if i.val < 627 then 626 else (if i.val < 628 then
      628 else 627))) else (if i.val < 632 then (if i.val < 630 then 629 else (if i.val < 631
      then 630 else 631)) else (if i.val < 634 then (if i.val < 633 then 633 else 632) else (if
      i.val < 635 then 638 else 639))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 640 else (if i.val < 638 then 641 else 634)) else
      (if i.val < 640 then 635 else (if i.val < 641 then 636 else 637))) else (if i.val < 645
      then (if i.val < 643 then 642 else (if i.val < 644 then 644 else 643)) else (if i.val <
      647 then (if i.val < 646 then 645 else 646) else (if i.val < 648 then 647 else 649))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 648 else (if i.val <
      651 then 654 else 655)) else (if i.val < 653 then 656 else (if i.val < 654 then 657 else
      650))) else (if i.val < 658 then (if i.val < 656 then 651 else (if i.val < 657 then 652
      else 653)) else (if i.val < 660 then (if i.val < 659 then 658 else 659) else (if i.val <
      661 then 661 else 660)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 662 else (if i.val < 664 then 663 else
      664)) else (if i.val < 666 then 665 else (if i.val < 667 then 666 else 667))) else (if
      i.val < 671 then (if i.val < 669 then 668 else (if i.val < 670 then 669 else 670)) else
      (if i.val < 672 then 671 else (if i.val < 673 then 672 else 673)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 674 else (if i.val < 676 then 675 else
      676)) else (if i.val < 678 then 677 else (if i.val < 679 then 678 else 679))) else (if
      i.val < 683 then (if i.val < 681 then 680 else (if i.val < 682 then 700 else 701)) else
      (if i.val < 685 then (if i.val < 684 then 702 else 703) else (if i.val < 686 then 704 else
      705))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 706 else (if i.val < 689 then 707 else 708)) else (if i.val < 691 then 709 else
      (if i.val < 692 then 710 else 711))) else (if i.val < 696 then (if i.val < 694 then 712
      else (if i.val < 695 then 713 else 714)) else (if i.val < 698 then (if i.val < 697 then
      715 else 716) else (if i.val < 699 then 717 else 718)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 681 else (if i.val < 702 then 682 else 683)) else
      (if i.val < 704 then 684 else (if i.val < 705 then 685 else 686))) else (if i.val < 709
      then (if i.val < 707 then 687 else (if i.val < 708 then 688 else 689)) else (if i.val <
      711 then (if i.val < 710 then 690 else 691) else (if i.val < 712 then 692 else 693)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 694 else (if i.val < 715 then 695 else 696))
      else (if i.val < 717 then 697 else (if i.val < 718 then 698 else 699))) else (if i.val <
      722 then (if i.val < 720 then 719 else (if i.val < 721 then 720 else 721)) else (if i.val
      < 723 then 722 else (if i.val < 724 then 723 else 724)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 725 else (if i.val < 727 then 726 else 745)) else
      (if i.val < 729 then 746 else (if i.val < 730 then 747 else 748))) else (if i.val < 734
      then (if i.val < 732 then 749 else (if i.val < 733 then 750 else 751)) else (if i.val <
      736 then (if i.val < 735 then 752 else 753) else (if i.val < 737 then 754 else 755)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      756 else (if i.val < 740 then 757 else 758)) else (if i.val < 742 then 759 else (if i.val
      < 743 then 760 else 761))) else (if i.val < 747 then (if i.val < 745 then 762 else (if
      i.val < 746 then 727 else 728)) else (if i.val < 749 then (if i.val < 748 then 729 else
      730) else (if i.val < 750 then 731 else 732)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 733 else (if i.val < 753 then 734 else 735)) else (if i.val <
      755 then 736 else (if i.val < 756 then 737 else 738))) else (if i.val < 760 then (if i.val
      < 758 then 739 else (if i.val < 759 then 740 else 741)) else (if i.val < 762 then (if
      i.val < 761 then 742 else 743) else (if i.val < 763 then 744 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 772 else 771)) else (if i.val < 774 then 773 else (if i.val < 775
      then 774 else 777)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      778 else (if i.val < 778 then 775 else 776)) else (if i.val < 780 then 779 else (if i.val
      < 781 then 780 else 781))) else (if i.val < 785 then (if i.val < 783 then 782 else (if
      i.val < 784 then 785 else 786)) else (if i.val < 787 then (if i.val < 786 then 783 else
      784) else (if i.val < 788 then 787 else 788))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 797 else (if i.val < 791 then 798 else
      799)) else (if i.val < 793 then 800 else (if i.val < 794 then 801 else 802))) else (if
      i.val < 798 then (if i.val < 796 then 803 else (if i.val < 797 then 804 else 789)) else
      (if i.val < 800 then (if i.val < 799 then 790 else 791) else (if i.val < 801 then 792 else
      793)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 794 else (if
      i.val < 804 then 795 else 796)) else (if i.val < 806 then 805 else (if i.val < 807 then
      807 else 806))) else (if i.val < 811 then (if i.val < 809 then 808 else (if i.val < 810
      then 810 else 809)) else (if i.val < 813 then (if i.val < 812 then 811 else 812) else (if
      i.val < 814 then 814 else 813)))))))))))
  invFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 0 else (if i.val < 2 then 1 else 2)) else (if i.val < 4 then 3 else (if i.val < 5
      then 7 else 8))) else (if i.val < 9 then (if i.val < 7 then 9 else (if i.val < 8 then 4
      else 5)) else (if i.val < 10 then 6 else (if i.val < 11 then 10 else 12)))) else (if i.val
      < 18 then (if i.val < 15 then (if i.val < 13 then 11 else (if i.val < 14 then 13 else 14))
      else (if i.val < 16 then 19 else (if i.val < 17 then 20 else 21))) else (if i.val < 21
      then (if i.val < 19 then 22 else (if i.val < 20 then 15 else 16)) else (if i.val < 23 then
      (if i.val < 22 then 17 else 18) else (if i.val < 24 then 23 else 24))))) else (if i.val <
      37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 27 else (if i.val < 27
      then 28 else 25)) else (if i.val < 29 then 26 else (if i.val < 30 then 29 else 30))) else
      (if i.val < 34 then (if i.val < 32 then 33 else (if i.val < 33 then 32 else 31)) else (if
      i.val < 35 then 39 else (if i.val < 36 then 40 else 41)))) else (if i.val < 43 then (if
      i.val < 40 then (if i.val < 38 then 42 else (if i.val < 39 then 43 else 34)) else (if
      i.val < 41 then 35 else (if i.val < 42 then 36 else 37))) else (if i.val < 46 then (if
      i.val < 44 then 38 else (if i.val < 45 then 44 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 47 else 46) else (if i.val < 49 then 48 else 49)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 50
      else (if i.val < 52 then 51 else 52)) else (if i.val < 54 then 53 else (if i.val < 55 then
      54 else 55))) else (if i.val < 59 then (if i.val < 57 then 56 else (if i.val < 58 then 64
      else 65)) else (if i.val < 60 then 66 else (if i.val < 61 then 67 else 68)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 69 else (if i.val < 64 then 70
      else 57)) else (if i.val < 66 then 58 else (if i.val < 67 then 59 else 60))) else (if
      i.val < 71 then (if i.val < 69 then 61 else (if i.val < 70 then 62 else 63)) else (if
      i.val < 73 then (if i.val < 72 then 71 else 73) else (if i.val < 74 then 72 else 74)))))
      else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then 82
      else (if i.val < 77 then 83 else 84)) else (if i.val < 79 then 85 else (if i.val < 80 then
      86 else 87))) else (if i.val < 84 then (if i.val < 82 then 88 else (if i.val < 83 then 75
      else 76)) else (if i.val < 86 then (if i.val < 85 then 77 else 78) else (if i.val < 87
      then 79 else 80)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then 81
      else (if i.val < 90 then 89 else 91)) else (if i.val < 92 then 90 else (if i.val < 93 then
      92 else 95))) else (if i.val < 97 then (if i.val < 95 then 96 else (if i.val < 96 then 93
      else 94)) else (if i.val < 99 then (if i.val < 98 then 97 else 102) else (if i.val < 100
      then 103 else 104))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113
      then (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 105 else (if i.val <
      103 then 98 else 99)) else (if i.val < 105 then 100 else (if i.val < 106 then 101 else
      106))) else (if i.val < 110 then (if i.val < 108 then 107 else (if i.val < 109 then 108
      else 112)) else (if i.val < 111 then 113 else (if i.val < 112 then 114 else 109)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 110 else (if i.val < 115
      then 111 else 117)) else (if i.val < 117 then 118 else (if i.val < 118 then 115 else
      116))) else (if i.val < 122 then (if i.val < 120 then 120 else (if i.val < 121 then 119
      else 121)) else (if i.val < 124 then (if i.val < 123 then 122 else 123) else (if i.val <
      125 then 124 else 125))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 126 else (if i.val < 128 then 127 else 128)) else (if i.val <
      130 then 129 else (if i.val < 131 then 130 else 131))) else (if i.val < 135 then (if i.val
      < 133 then 132 else (if i.val < 134 then 133 else 134)) else (if i.val < 137 then (if
      i.val < 136 then 135 else 136) else (if i.val < 138 then 137 else 138)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 139 else (if i.val < 141 then 155 else
      156)) else (if i.val < 143 then 157 else (if i.val < 144 then 158 else 159))) else (if
      i.val < 148 then (if i.val < 146 then 160 else (if i.val < 147 then 161 else 162)) else
      (if i.val < 150 then (if i.val < 149 then 163 else 164) else (if i.val < 151 then 165 else
      166)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 167 else (if i.val < 154 then 168 else 169)) else (if i.val
      < 156 then 140 else (if i.val < 157 then 141 else 142))) else (if i.val < 161 then (if
      i.val < 159 then 143 else (if i.val < 160 then 144 else 145)) else (if i.val < 162 then
      146 else (if i.val < 163 then 147 else 148)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 149 else (if i.val < 166 then 150 else 151)) else (if i.val <
      168 then 152 else (if i.val < 169 then 153 else 154))) else (if i.val < 173 then (if i.val
      < 171 then 170 else (if i.val < 172 then 172 else 171)) else (if i.val < 175 then (if
      i.val < 174 then 173 else 174) else (if i.val < 176 then 175 else 177))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 176 else (if
      i.val < 179 then 178 else 179)) else (if i.val < 181 then 180 else (if i.val < 182 then
      181 else 201))) else (if i.val < 186 then (if i.val < 184 then 202 else (if i.val < 185
      then 203 else 204)) else (if i.val < 188 then (if i.val < 187 then 205 else 206) else (if
      i.val < 189 then 207 else 208)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 209 else (if i.val < 192 then 210 else 211)) else (if i.val < 194 then 212 else
      (if i.val < 195 then 213 else 214))) else (if i.val < 199 then (if i.val < 197 then 215
      else (if i.val < 198 then 216 else 217)) else (if i.val < 201 then (if i.val < 200 then
      218 else 219) else (if i.val < 202 then 182 else 183)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 184 else (if i.val < 205 then 185 else 186)) else (if
      i.val < 207 then 187 else (if i.val < 208 then 188 else 189))) else (if i.val < 212 then
      (if i.val < 210 then 190 else (if i.val < 211 then 191 else 192)) else (if i.val < 213
      then 193 else (if i.val < 214 then 194 else 195)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 196 else (if i.val < 217 then 197 else 198)) else (if i.val
      < 219 then 199 else (if i.val < 220 then 200 else 220))) else (if i.val < 224 then (if
      i.val < 222 then 222 else (if i.val < 223 then 221 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 226 else 228))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 227 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 234))) else (if i.val < 237 then (if i.val < 235 then 233 else (if i.val <
      236 then 235 else 236)) else (if i.val < 239 then (if i.val < 238 then 238 else 237) else
      (if i.val < 240 then 239 else 246)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 247 else (if i.val < 243 then 244 else 245)) else (if i.val < 245 then
      242 else (if i.val < 246 then 243 else 240))) else (if i.val < 250 then (if i.val < 248
      then 241 else (if i.val < 249 then 260 else 261)) else (if i.val < 252 then (if i.val <
      251 then 262 else 263) else (if i.val < 253 then 264 else 265)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      266 else (if i.val < 256 then 267 else 268)) else (if i.val < 258 then 269 else (if i.val
      < 259 then 270 else 271))) else (if i.val < 263 then (if i.val < 261 then 248 else (if
      i.val < 262 then 249 else 250)) else (if i.val < 264 then 251 else (if i.val < 265 then
      252 else 253)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 254
      else (if i.val < 268 then 255 else 256)) else (if i.val < 270 then 257 else (if i.val <
      271 then 258 else 259))) else (if i.val < 275 then (if i.val < 273 then 272 else (if i.val
      < 274 then 273 else 275)) else (if i.val < 277 then (if i.val < 276 then 274 else 277)
      else (if i.val < 278 then 276 else 279))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 278 else (if i.val < 281 then 280 else 281))
      else (if i.val < 283 then 282 else (if i.val < 284 then 284 else 283))) else (if i.val <
      288 then (if i.val < 286 then 288 else (if i.val < 287 then 289 else 290)) else (if i.val
      < 290 then (if i.val < 289 then 285 else 286) else (if i.val < 291 then 287 else 291))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 293 else (if i.val <
      294 then 292 else 294)) else (if i.val < 296 then 295 else (if i.val < 297 then 300 else
      301))) else (if i.val < 301 then (if i.val < 299 then 302 else (if i.val < 300 then 303
      else 296)) else (if i.val < 303 then (if i.val < 302 then 297 else 298) else (if i.val <
      304 then 299 else 304))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 306 else (if i.val
      < 307 then 305 else 307)) else (if i.val < 309 then 308 else (if i.val < 310 then 310 else
      309))) else (if i.val < 314 then (if i.val < 312 then 315 else (if i.val < 313 then 316
      else 317)) else (if i.val < 315 then 318 else (if i.val < 316 then 311 else 312)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 313 else (if i.val < 319
      then 314 else 319)) else (if i.val < 321 then 320 else (if i.val < 322 then 322 else
      321))) else (if i.val < 326 then (if i.val < 324 then 344 else (if i.val < 325 then 345
      else 346)) else (if i.val < 328 then (if i.val < 327 then 347 else 348) else (if i.val <
      329 then 349 else 350))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 351 else (if i.val < 332 then 352 else 353)) else (if i.val <
      334 then 354 else (if i.val < 335 then 355 else 356))) else (if i.val < 339 then (if i.val
      < 337 then 357 else (if i.val < 338 then 358 else 359)) else (if i.val < 341 then (if
      i.val < 340 then 360 else 343) else (if i.val < 342 then 341 else 342)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 340 else (if i.val < 345 then 323 else
      324)) else (if i.val < 347 then 325 else (if i.val < 348 then 326 else 327))) else (if
      i.val < 352 then (if i.val < 350 then 328 else (if i.val < 351 then 329 else 330)) else
      (if i.val < 354 then (if i.val < 353 then 331 else 332) else (if i.val < 355 then 333 else
      334)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 335 else (if i.val < 358 then 336 else 337)) else (if i.val
      < 360 then 338 else (if i.val < 361 then 339 else 362))) else (if i.val < 365 then (if
      i.val < 363 then 361 else (if i.val < 364 then 363 else 364)) else (if i.val < 366 then
      366 else (if i.val < 367 then 365 else 367)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 369 else (if i.val < 370 then 368 else 370)) else (if i.val <
      372 then 374 else (if i.val < 373 then 375 else 376))) else (if i.val < 377 then (if i.val
      < 375 then 371 else (if i.val < 376 then 372 else 373)) else (if i.val < 379 then (if
      i.val < 378 then 377 else 378) else (if i.val < 380 then 379 else 380))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 381 else (if
      i.val < 383 then 382 else 383)) else (if i.val < 385 then 391 else (if i.val < 386 then
      392 else 393))) else (if i.val < 390 then (if i.val < 388 then 394 else (if i.val < 389
      then 395 else 396)) else (if i.val < 392 then (if i.val < 391 then 397 else 384) else (if
      i.val < 393 then 385 else 386)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 387 else (if i.val < 396 then 388 else 389)) else (if i.val < 398 then 390 else
      (if i.val < 399 then 398 else 404))) else (if i.val < 403 then (if i.val < 401 then 405
      else (if i.val < 402 then 406 else 407)) else (if i.val < 405 then (if i.val < 404 then
      408 else 399) else (if i.val < 406 then 400 else 401))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 402 else (if i.val < 409 then
      403 else 409)) else (if i.val < 411 then 412 else (if i.val < 412 then 413 else 410)))
      else (if i.val < 416 then (if i.val < 414 then 411 else (if i.val < 415 then 414 else
      416)) else (if i.val < 417 then 415 else (if i.val < 418 then 417 else 418)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 419 else (if i.val < 421 then
      420 else 421)) else (if i.val < 423 then 422 else (if i.val < 424 then 423 else 424)))
      else (if i.val < 428 then (if i.val < 426 then 425 else (if i.val < 427 then 426 else
      437)) else (if i.val < 430 then (if i.val < 429 then 438 else 439) else (if i.val < 431
      then 440 else 441))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 442 else (if i.val < 434 then 443 else 444)) else (if i.val < 436
      then 445 else (if i.val < 437 then 446 else 427))) else (if i.val < 441 then (if i.val <
      439 then 428 else (if i.val < 440 then 429 else 430)) else (if i.val < 443 then (if i.val
      < 442 then 431 else 432) else (if i.val < 444 then 433 else 434)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 435 else (if i.val < 447 then 436 else
      447)) else (if i.val < 449 then 448 else (if i.val < 450 then 449 else 460))) else (if
      i.val < 454 then (if i.val < 452 then 461 else (if i.val < 453 then 462 else 463)) else
      (if i.val < 456 then (if i.val < 455 then 464 else 465) else (if i.val < 457 then 466 else
      467)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 468 else (if i.val < 460 then 469 else 450)) else (if i.val
      < 462 then 451 else (if i.val < 463 then 452 else 453))) else (if i.val < 467 then (if
      i.val < 465 then 454 else (if i.val < 466 then 455 else 456)) else (if i.val < 468 then
      457 else (if i.val < 469 then 458 else 459)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 473 else (if i.val < 475 then 476 else 477))) else (if i.val < 479 then (if i.val
      < 477 then 474 else (if i.val < 478 then 475 else 478)) else (if i.val < 481 then (if
      i.val < 480 then 479 else 481) else (if i.val < 482 then 480 else 482))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 486 else (if
      i.val < 485 then 487 else 488)) else (if i.val < 487 then 483 else (if i.val < 488 then
      484 else 485))) else (if i.val < 492 then (if i.val < 490 then 489 else (if i.val < 491
      then 491 else 490)) else (if i.val < 494 then (if i.val < 493 then 492 else 494) else (if
      i.val < 495 then 493 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 496 else (if i.val < 498 then 498 else 497)) else (if i.val < 500 then 499 else
      (if i.val < 501 then 500 else 501))) else (if i.val < 505 then (if i.val < 503 then 502
      else (if i.val < 504 then 506 else 507)) else (if i.val < 507 then (if i.val < 506 then
      508 else 503) else (if i.val < 508 then 504 else 505))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 509 else (if i.val < 511 then 510 else 512)) else (if i.val < 513 then 511 else
      (if i.val < 514 then 513 else 514))) else (if i.val < 518 then (if i.val < 516 then 519
      else (if i.val < 517 then 520 else 521)) else (if i.val < 519 then 522 else (if i.val <
      520 then 515 else 516)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 517 else (if i.val < 523 then 518 else 523)) else (if i.val < 525 then 524 else (if
      i.val < 526 then 526 else 525))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 529)) else (if i.val < 532 then (if i.val < 531 then 531
      else 530) else (if i.val < 533 then 538 else 539))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 540 else (if i.val < 536 then 541
      else 542)) else (if i.val < 538 then 543 else (if i.val < 539 then 532 else 533))) else
      (if i.val < 543 then (if i.val < 541 then 534 else (if i.val < 542 then 535 else 536))
      else (if i.val < 545 then (if i.val < 544 then 537 else 544) else (if i.val < 546 then 545
      else 547)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 546 else
      (if i.val < 549 then 549 else 548)) else (if i.val < 551 then 551 else (if i.val < 552
      then 550 else 552))) else (if i.val < 556 then (if i.val < 554 then 553 else (if i.val <
      555 then 554 else 556)) else (if i.val < 558 then (if i.val < 557 then 555 else 561) else
      (if i.val < 559 then 562 else 563)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 564 else (if i.val < 562 then
      557 else 558)) else (if i.val < 564 then 559 else (if i.val < 565 then 560 else 565)))
      else (if i.val < 569 then (if i.val < 567 then 567 else (if i.val < 568 then 566 else
      568)) else (if i.val < 570 then 569 else (if i.val < 571 then 574 else 575)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 576 else (if i.val < 574 then
      577 else 570)) else (if i.val < 576 then 571 else (if i.val < 577 then 572 else 573)))
      else (if i.val < 581 then (if i.val < 579 then 578 else (if i.val < 580 then 580 else
      579)) else (if i.val < 583 then (if i.val < 582 then 581 else 582) else (if i.val < 584
      then 583 else 585))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 584 else (if i.val < 587 then 590 else 591)) else (if i.val < 589
      then 592 else (if i.val < 590 then 593 else 586))) else (if i.val < 594 then (if i.val <
      592 then 587 else (if i.val < 593 then 588 else 589)) else (if i.val < 596 then (if i.val
      < 595 then 594 else 595) else (if i.val < 597 then 597 else 596)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 598 else (if i.val < 600 then 599 else
      601)) else (if i.val < 602 then 600 else (if i.val < 603 then 606 else 607))) else (if
      i.val < 607 then (if i.val < 605 then 608 else (if i.val < 606 then 609 else 602)) else
      (if i.val < 609 then (if i.val < 608 then 603 else 604) else (if i.val < 610 then 605 else
      611)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 610 else (if
      i.val < 613 then 612 else 613)) else (if i.val < 615 then 614 else (if i.val < 616 then
      615 else 617))) else (if i.val < 620 then (if i.val < 618 then 616 else (if i.val < 619
      then 622 else 623)) else (if i.val < 621 then 624 else (if i.val < 622 then 625 else
      618)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 619 else (if
      i.val < 625 then 620 else 621)) else (if i.val < 627 then 626 else (if i.val < 628 then
      628 else 627))) else (if i.val < 632 then (if i.val < 630 then 629 else (if i.val < 631
      then 630 else 631)) else (if i.val < 634 then (if i.val < 633 then 633 else 632) else (if
      i.val < 635 then 638 else 639))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 640 else (if i.val < 638 then 641 else 634)) else
      (if i.val < 640 then 635 else (if i.val < 641 then 636 else 637))) else (if i.val < 645
      then (if i.val < 643 then 642 else (if i.val < 644 then 644 else 643)) else (if i.val <
      647 then (if i.val < 646 then 645 else 646) else (if i.val < 648 then 647 else 649))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 648 else (if i.val <
      651 then 654 else 655)) else (if i.val < 653 then 656 else (if i.val < 654 then 657 else
      650))) else (if i.val < 658 then (if i.val < 656 then 651 else (if i.val < 657 then 652
      else 653)) else (if i.val < 660 then (if i.val < 659 then 658 else 659) else (if i.val <
      661 then 661 else 660)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 662 else (if i.val < 664 then 663 else
      664)) else (if i.val < 666 then 665 else (if i.val < 667 then 666 else 667))) else (if
      i.val < 671 then (if i.val < 669 then 668 else (if i.val < 670 then 669 else 670)) else
      (if i.val < 672 then 671 else (if i.val < 673 then 672 else 673)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 674 else (if i.val < 676 then 675 else
      676)) else (if i.val < 678 then 677 else (if i.val < 679 then 678 else 679))) else (if
      i.val < 683 then (if i.val < 681 then 680 else (if i.val < 682 then 700 else 701)) else
      (if i.val < 685 then (if i.val < 684 then 702 else 703) else (if i.val < 686 then 704 else
      705))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 706 else (if i.val < 689 then 707 else 708)) else (if i.val < 691 then 709 else
      (if i.val < 692 then 710 else 711))) else (if i.val < 696 then (if i.val < 694 then 712
      else (if i.val < 695 then 713 else 714)) else (if i.val < 698 then (if i.val < 697 then
      715 else 716) else (if i.val < 699 then 717 else 718)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 681 else (if i.val < 702 then 682 else 683)) else
      (if i.val < 704 then 684 else (if i.val < 705 then 685 else 686))) else (if i.val < 709
      then (if i.val < 707 then 687 else (if i.val < 708 then 688 else 689)) else (if i.val <
      711 then (if i.val < 710 then 690 else 691) else (if i.val < 712 then 692 else 693)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 694 else (if i.val < 715 then 695 else 696))
      else (if i.val < 717 then 697 else (if i.val < 718 then 698 else 699))) else (if i.val <
      722 then (if i.val < 720 then 719 else (if i.val < 721 then 720 else 721)) else (if i.val
      < 723 then 722 else (if i.val < 724 then 723 else 724)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 725 else (if i.val < 727 then 726 else 745)) else
      (if i.val < 729 then 746 else (if i.val < 730 then 747 else 748))) else (if i.val < 734
      then (if i.val < 732 then 749 else (if i.val < 733 then 750 else 751)) else (if i.val <
      736 then (if i.val < 735 then 752 else 753) else (if i.val < 737 then 754 else 755)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      756 else (if i.val < 740 then 757 else 758)) else (if i.val < 742 then 759 else (if i.val
      < 743 then 760 else 761))) else (if i.val < 747 then (if i.val < 745 then 762 else (if
      i.val < 746 then 727 else 728)) else (if i.val < 749 then (if i.val < 748 then 729 else
      730) else (if i.val < 750 then 731 else 732)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 733 else (if i.val < 753 then 734 else 735)) else (if i.val <
      755 then 736 else (if i.val < 756 then 737 else 738))) else (if i.val < 760 then (if i.val
      < 758 then 739 else (if i.val < 759 then 740 else 741)) else (if i.val < 762 then (if
      i.val < 761 then 742 else 743) else (if i.val < 763 then 744 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 772 else 771)) else (if i.val < 774 then 773 else (if i.val < 775
      then 774 else 777)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      778 else (if i.val < 778 then 775 else 776)) else (if i.val < 780 then 779 else (if i.val
      < 781 then 780 else 781))) else (if i.val < 785 then (if i.val < 783 then 782 else (if
      i.val < 784 then 785 else 786)) else (if i.val < 787 then (if i.val < 786 then 783 else
      784) else (if i.val < 788 then 787 else 788))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 797 else (if i.val < 791 then 798 else
      799)) else (if i.val < 793 then 800 else (if i.val < 794 then 801 else 802))) else (if
      i.val < 798 then (if i.val < 796 then 803 else (if i.val < 797 then 804 else 789)) else
      (if i.val < 800 then (if i.val < 799 then 790 else 791) else (if i.val < 801 then 792 else
      793)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 794 else (if
      i.val < 804 then 795 else 796)) else (if i.val < 806 then 805 else (if i.val < 807 then
      807 else 806))) else (if i.val < 811 then (if i.val < 809 then 808 else (if i.val < 810
      then 810 else 809)) else (if i.val < 813 then (if i.val < 812 then 811 else 812) else (if
      i.val < 814 then 814 else 813)))))))))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed vertex, edge and branch bijections for this frame permutation. -/
def hint1 : Fin 815 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
    (if i.val < 25 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 37 then ⟨[0, 1], [0], [false]⟩
    else (if i.val < 43 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 46 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 48 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else (if i.val < 105 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val
    < 106 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩))) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 119 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 122 then (if i.val < 120
    then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 121 then ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else ⟨[0,
    1, 2], [0, 1], [false, false]⟩))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2],
    [0, 1], [false, false]⟩)) else (if i.val < 305 then (if i.val < 254 then (if i.val < 228
    then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 241 then (if i.val < 234 then ⟨[0,
    1, 2], [0, 1], [false, false]⟩ else (if i.val < 237 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else (if i.val < 239 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 240 then ⟨[0,
    1, 2], [0, 1], [false, false]⟩ else ⟨[0, 2, 1], [0, 1], [false, true]⟩)))) else (if i.val <
    247 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else (if i.val < 250 then (if i.val < 248 then
    ⟨[0, 2, 1], [0, 1], [false, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1,
    2], [0, 1], [false, false]⟩)))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else (if i.val <
    356 then (if i.val < 330 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 343 then
    (if i.val < 336 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 339 then ⟨[0, 1,
    2], [0, 1], [false, false]⟩ else (if i.val < 341 then (if i.val < 340 then ⟨[0, 1, 2], [0,
    1], [false, false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩) else ⟨[2, 1, 0], [1, 0], [true,
    true]⟩))) else (if i.val < 349 then (if i.val < 346 then (if i.val < 344 then ⟨[2, 1, 0],
    [1, 0], [true, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2], [0, 1],
    [false, false]⟩) else ⟨[0, 1, 2], [0, 1], [false, false]⟩))) else (if i.val < 381 then (if
    i.val < 368 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 374 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else (if i.val < 377 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩))) else ⟨[0, 1, 2, 3], [0, 1, 2], [false,
    false, false]⟩)))) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then ⟨[0,
    1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 483 then (if i.val < 470 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 476 then ⟨[0, 1, 2, 3],
    [0, 1, 2], [false, false, false]⟩ else (if i.val < 479 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 481 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩ else (if i.val < 482 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0,
    3, 2, 1], [0, 2, 1], [false, true, true]⟩))))) else (if i.val < 496 then (if i.val < 489
    then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩) else (if i.val < 502 then (if i.val < 499 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else ⟨[0, 1], [0, 1], [false, false]⟩) else ⟨[0, 1], [0, 1], [false, false]⟩)))) else ⟨[0,
    1], [0, 1], [false, false]⟩) else (if i.val < 713 then (if i.val < 662 then ⟨[0, 1], [0, 1],
    [false, false]⟩ else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩) else (if i.val < 764
    then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 789 then ⟨[0, 1, 2], [0,
    1, 2], [false, false, false]⟩ else (if i.val < 802 then ⟨[0, 1, 2], [0, 1, 2], [false,
    false, false]⟩ else (if i.val < 808 then (if i.val < 805 then ⟨[0, 1, 2], [0, 1, 2], [false,
    false, false]⟩ else ⟨[0, 1], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1], [0, 1, 2],
    [false, false, false]⟩))))))))

/-- The kernel checks the supplied bijections without repeating permutation search. -/
theorem hints_valid1 : ∀ i, (hint1 i).check ((L24Graphs.graph i).relabel labels1)
    (L24Graphs.graph (destination1 i)) = true := by
  decide +kernel

/-- Every column is transported as a full decorated labelled graph. -/
theorem covered1 : ∀ i, ((L24Graphs.graph i).relabel labels1).isomorphic?
    (L24Graphs.graph (destination1 i)) = true := by
  intro i
  exact (hint1 i).check_sound _ _ (hints_valid1 i)

/-- The 2-th permutation of the three free markings; old labels map covariantly. -/
def labels2 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 0, 3]
  invFun := ![2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A candidate bijection of the held frame columns. -/
def destination2 : Equiv.Perm (Fin 815) where
  toFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 16 else (if i.val < 2 then 18 else 15)) else (if i.val < 4 then 17 else (if i.val <
      5 then 6 else 5))) else (if i.val < 9 then (if i.val < 7 then 4 else (if i.val < 8 then 31
      else 32)) else (if i.val < 10 then 33 else (if i.val < 11 then 35 else 34)))) else (if
      i.val < 18 then (if i.val < 15 then (if i.val < 13 then 36 else (if i.val < 14 then 37
      else 38)) else (if i.val < 16 then 2 else (if i.val < 17 then 0 else 3))) else (if i.val <
      21 then (if i.val < 19 then 1 else (if i.val < 20 then 19 else 20)) else (if i.val < 23
      then (if i.val < 22 then 21 else 22) else (if i.val < 24 then 25 else 26))))) else (if
      i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 23 else (if
      i.val < 27 then 24 else 27)) else (if i.val < 29 then 28 else (if i.val < 30 then 29 else
      30))) else (if i.val < 34 then (if i.val < 32 then 7 else (if i.val < 33 then 8 else 9))
      else (if i.val < 35 then 11 else (if i.val < 36 then 10 else 12)))) else (if i.val < 43
      then (if i.val < 40 then (if i.val < 38 then 13 else (if i.val < 39 then 14 else 41)) else
      (if i.val < 41 then 40 else (if i.val < 42 then 39 else 42))) else (if i.val < 46 then (if
      i.val < 44 then 43 else (if i.val < 45 then 46 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 44 else 47) else (if i.val < 49 then 77 else 78)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 75
      else (if i.val < 52 then 76 else 69)) else (if i.val < 54 then 68 else (if i.val < 55 then
      80 else 79))) else (if i.val < 59 then (if i.val < 57 then 81 else (if i.val < 58 then 59
      else 60)) else (if i.val < 60 then 57 else (if i.val < 61 then 58 else 61)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 62 else (if i.val < 64 then 63
      else 93)) else (if i.val < 66 then 94 else (if i.val < 67 then 95 else 96))) else (if
      i.val < 71 then (if i.val < 69 then 53 else (if i.val < 70 then 52 else 97)) else (if
      i.val < 73 then (if i.val < 72 then 99 else 98) else (if i.val < 74 then 100 else 101)))))
      else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then 50
      else (if i.val < 77 then 51 else 48)) else (if i.val < 79 then 49 else (if i.val < 80 then
      55 else 54))) else (if i.val < 84 then (if i.val < 82 then 56 else (if i.val < 83 then 82
      else 83)) else (if i.val < 86 then (if i.val < 85 then 84 else 85) else (if i.val < 87
      then 86 else 87)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then 88
      else (if i.val < 90 then 90 else 89)) else (if i.val < 92 then 91 else (if i.val < 93 then
      92 else 64))) else (if i.val < 97 then (if i.val < 95 then 65 else (if i.val < 96 then 66
      else 67)) else (if i.val < 99 then (if i.val < 98 then 70 else 72) else (if i.val < 100
      then 71 else 73))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then
      (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 74 else (if i.val < 103
      then 104 else 103)) else (if i.val < 105 then 102 else (if i.val < 106 then 105 else
      116))) else (if i.val < 110 then (if i.val < 108 then 115 else (if i.val < 109 then 114
      else 110)) else (if i.val < 111 then 109 else (if i.val < 112 then 111 else 119)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 120 else (if i.val < 115
      then 108 else 107)) else (if i.val < 117 then 106 else (if i.val < 118 then 117 else
      118))) else (if i.val < 122 then (if i.val < 120 then 112 else (if i.val < 121 then 113
      else 183)) else (if i.val < 124 then (if i.val < 123 then 182 else 184) else (if i.val <
      125 then 185 else 186))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 187 else (if i.val < 128 then 189 else 188)) else (if i.val <
      130 then 190 else (if i.val < 131 then 199 else 200))) else (if i.val < 135 then (if i.val
      < 133 then 196 else (if i.val < 134 then 197 else 198)) else (if i.val < 137 then (if
      i.val < 136 then 193 else 194) else (if i.val < 138 then 195 else 191)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 192 else (if i.val < 141 then 141 else
      140)) else (if i.val < 143 then 142 else (if i.val < 144 then 143 else 145))) else (if
      i.val < 148 then (if i.val < 146 then 144 else (if i.val < 147 then 146 else 153)) else
      (if i.val < 150 then (if i.val < 149 then 154 else 151) else (if i.val < 151 then 152 else
      149)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 150 else (if i.val < 154 then 147 else 148)) else (if i.val
      < 156 then 233 else (if i.val < 157 then 234 else 235))) else (if i.val < 161 then (if
      i.val < 159 then 236 else (if i.val < 160 then 237 else 238)) else (if i.val < 162 then
      239 else (if i.val < 163 then 240 else 241)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 242 else (if i.val < 166 then 243 else 244)) else (if i.val <
      168 then 245 else (if i.val < 169 then 246 else 247))) else (if i.val < 173 then (if i.val
      < 171 then 249 else (if i.val < 172 then 248 else 250)) else (if i.val < 175 then (if
      i.val < 174 then 251 else 252) else (if i.val < 176 then 253 else 254))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 255 else (if
      i.val < 179 then 256 else 257)) else (if i.val < 181 then 258 else (if i.val < 182 then
      259 else 122))) else (if i.val < 186 then (if i.val < 184 then 121 else (if i.val < 185
      then 123 else 124)) else (if i.val < 188 then (if i.val < 187 then 125 else 126) else (if
      i.val < 189 then 128 else 127)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 129 else (if i.val < 192 then 138 else 139)) else (if i.val < 194 then 135 else
      (if i.val < 195 then 136 else 137))) else (if i.val < 199 then (if i.val < 197 then 132
      else (if i.val < 198 then 133 else 134)) else (if i.val < 201 then (if i.val < 200 then
      130 else 131) else (if i.val < 202 then 201 else 202)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 203 else (if i.val < 205 then 204 else 205)) else (if
      i.val < 207 then 206 else (if i.val < 208 then 207 else 208))) else (if i.val < 212 then
      (if i.val < 210 then 209 else (if i.val < 211 then 210 else 211)) else (if i.val < 213
      then 212 else (if i.val < 214 then 213 else 214)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 215 else (if i.val < 217 then 216 else 217)) else (if i.val
      < 219 then 218 else (if i.val < 220 then 219 else 221))) else (if i.val < 224 then (if
      i.val < 222 then 220 else (if i.val < 223 then 222 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 227 else 226))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 228 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 155))) else (if i.val < 237 then (if i.val < 235 then 156 else (if i.val <
      236 then 157 else 158)) else (if i.val < 239 then (if i.val < 238 then 159 else 160) else
      (if i.val < 240 then 161 else 162)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 163 else (if i.val < 243 then 164 else 165)) else (if i.val < 245 then
      166 else (if i.val < 246 then 167 else 168))) else (if i.val < 250 then (if i.val < 248
      then 169 else (if i.val < 249 then 171 else 170)) else (if i.val < 252 then (if i.val <
      251 then 172 else 173) else (if i.val < 253 then 174 else 175)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      176 else (if i.val < 256 then 177 else 178)) else (if i.val < 258 then 179 else (if i.val
      < 259 then 180 else 181))) else (if i.val < 263 then (if i.val < 261 then 262 else (if
      i.val < 262 then 261 else 260)) else (if i.val < 264 then 263 else (if i.val < 265 then
      264 else 265)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 267
      else (if i.val < 268 then 266 else 268)) else (if i.val < 270 then 269 else (if i.val <
      271 then 270 else 271))) else (if i.val < 275 then (if i.val < 273 then 274 else (if i.val
      < 274 then 273 else 272)) else (if i.val < 277 then (if i.val < 276 then 275 else 276)
      else (if i.val < 278 then 295 else 296))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 297 else (if i.val < 281 then 299 else 298))
      else (if i.val < 283 then 283 else (if i.val < 284 then 282 else 284))) else (if i.val <
      288 then (if i.val < 286 then 285 else (if i.val < 287 then 287 else 286)) else (if i.val
      < 290 then (if i.val < 289 then 308 else 309) else (if i.val < 291 then 310 else 312))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 311 else (if i.val <
      294 then 313 else 314)) else (if i.val < 296 then 277 else (if i.val < 297 then 278 else
      279))) else (if i.val < 301 then (if i.val < 299 then 281 else (if i.val < 300 then 280
      else 301)) else (if i.val < 303 then (if i.val < 302 then 300 else 302) else (if i.val <
      304 then 303 else 305))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 304 else (if i.val
      < 307 then 306 else 307)) else (if i.val < 309 then 288 else (if i.val < 310 then 289 else
      290))) else (if i.val < 314 then (if i.val < 312 then 292 else (if i.val < 313 then 291
      else 293)) else (if i.val < 315 then 294 else (if i.val < 316 then 317 else 316)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 315 else (if i.val < 319
      then 318 else 321)) else (if i.val < 321 then 320 else (if i.val < 322 then 319 else
      322))) else (if i.val < 326 then (if i.val < 324 then 333 else (if i.val < 325 then 335
      else 334)) else (if i.val < 328 then (if i.val < 327 then 326 else 328) else (if i.val <
      329 then 327 else 340))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 342 else (if i.val < 332 then 341 else 343)) else (if i.val <
      334 then 323 else (if i.val < 335 then 325 else 324))) else (if i.val < 339 then (if i.val
      < 337 then 336 else (if i.val < 338 then 338 else 337)) else (if i.val < 341 then (if
      i.val < 340 then 339 else 329) else (if i.val < 342 then 331 else 330)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 332 else (if i.val < 345 then 376 else
      375)) else (if i.val < 347 then 374 else (if i.val < 348 then 363 else 361))) else (if
      i.val < 352 then (if i.val < 350 then 362 else (if i.val < 351 then 353 else 351)) else
      (if i.val < 354 then (if i.val < 353 then 352 else 350) else (if i.val < 355 then 373 else
      371)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 372 else (if i.val < 358 then 370 else 368)) else (if i.val
      < 360 then 369 else (if i.val < 361 then 367 else 348))) else (if i.val < 365 then (if
      i.val < 363 then 349 else (if i.val < 364 then 347 else 366)) else (if i.val < 366 then
      365 else (if i.val < 367 then 364 else 360)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 358 else (if i.val < 370 then 359 else 357)) else (if i.val <
      372 then 355 else (if i.val < 373 then 356 else 354))) else (if i.val < 377 then (if i.val
      < 375 then 346 else (if i.val < 376 then 345 else 344)) else (if i.val < 379 then (if
      i.val < 378 then 401 else 402) else (if i.val < 380 then 399 else 400))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 395 else (if
      i.val < 383 then 396 else 403)) else (if i.val < 385 then 386 else (if i.val < 386 then
      387 else 384))) else (if i.val < 390 then (if i.val < 388 then 385 else (if i.val < 389
      then 388 else 389)) else (if i.val < 392 then (if i.val < 391 then 390 else 410) else (if
      i.val < 393 then 411 else 412)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 413 else (if i.val < 396 then 381 else 382)) else (if i.val < 398 then 414 else
      (if i.val < 399 then 415 else 379))) else (if i.val < 403 then (if i.val < 401 then 380
      else (if i.val < 402 then 377 else 378)) else (if i.val < 405 then (if i.val < 404 then
      383 else 404) else (if i.val < 406 then 405 else 406))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 407 else (if i.val < 409 then
      408 else 409)) else (if i.val < 411 then 391 else (if i.val < 412 then 392 else 393)))
      else (if i.val < 416 then (if i.val < 414 then 394 else (if i.val < 415 then 397 else
      398)) else (if i.val < 417 then 416 else (if i.val < 418 then 450 else 453)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 454 else (if i.val < 421 then
      451 else 452)) else (if i.val < 423 then 455 else (if i.val < 424 then 456 else 458)))
      else (if i.val < 428 then (if i.val < 426 then 457 else (if i.val < 427 then 459 else
      427)) else (if i.val < 430 then (if i.val < 429 then 430 else 431) else (if i.val < 431
      then 428 else 429))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 432 else (if i.val < 434 then 433 else 435)) else (if i.val < 436
      then 434 else (if i.val < 437 then 436 else 473))) else (if i.val < 441 then (if i.val <
      439 then 474 else (if i.val < 440 then 475 else 476)) else (if i.val < 443 then (if i.val
      < 442 then 477 else 478) else (if i.val < 444 then 479 else 480)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 481 else (if i.val < 447 then 482 else
      483)) else (if i.val < 449 then 484 else (if i.val < 450 then 485 else 417))) else (if
      i.val < 454 then (if i.val < 452 then 420 else (if i.val < 453 then 421 else 418)) else
      (if i.val < 456 then (if i.val < 455 then 419 else 422) else (if i.val < 457 then 423 else
      425)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 424 else (if i.val < 460 then 426 else 460)) else (if i.val
      < 462 then 461 else (if i.val < 463 then 462 else 463))) else (if i.val < 467 then (if
      i.val < 465 then 464 else (if i.val < 466 then 465 else 466)) else (if i.val < 468 then
      467 else (if i.val < 469 then 468 else 469)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 437 else (if i.val < 475 then 438 else 439))) else (if i.val < 479 then (if i.val
      < 477 then 440 else (if i.val < 478 then 441 else 442)) else (if i.val < 481 then (if
      i.val < 480 then 443 else 444) else (if i.val < 482 then 445 else 446))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 447 else (if
      i.val < 485 then 448 else 449)) else (if i.val < 487 then 486 else (if i.val < 488 then
      487 else 488))) else (if i.val < 492 then (if i.val < 490 then 493 else (if i.val < 491
      then 490 else 496)) else (if i.val < 494 then (if i.val < 493 then 497 else 489) else (if
      i.val < 495 then 494 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 491 else (if i.val < 498 then 492 else 498)) else (if i.val < 500 then 515 else
      (if i.val < 501 then 517 else 516))) else (if i.val < 505 then (if i.val < 503 then 518
      else (if i.val < 504 then 503 else 505)) else (if i.val < 507 then (if i.val < 506 then
      504 else 529) else (if i.val < 508 then 530 else 531))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 532 else (if i.val < 511 then 534 else 533)) else (if i.val < 513 then 535 else
      (if i.val < 514 then 536 else 537))) else (if i.val < 518 then (if i.val < 516 then 499
      else (if i.val < 517 then 501 else 500)) else (if i.val < 519 then 502 else (if i.val <
      520 then 519 else 520)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 521 else (if i.val < 523 then 522 else 523)) else (if i.val < 525 then 525 else (if
      i.val < 526 then 524 else 526))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 506)) else (if i.val < 532 then (if i.val < 531 then 507
      else 508) else (if i.val < 533 then 509 else 511))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 510 else (if i.val < 536 then 512
      else 513)) else (if i.val < 538 then 514 else (if i.val < 539 then 538 else 541))) else
      (if i.val < 543 then (if i.val < 541 then 540 else (if i.val < 542 then 539 else 542))
      else (if i.val < 545 then (if i.val < 544 then 543 else 546) else (if i.val < 546 then 545
      else 544)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 547 else
      (if i.val < 549 then 548 else 569)) else (if i.val < 551 then 570 else (if i.val < 552
      then 571 else 573))) else (if i.val < 556 then (if i.val < 554 then 572 else (if i.val <
      555 then 555 else 554)) else (if i.val < 558 then (if i.val < 557 then 556 else 557) else
      (if i.val < 559 then 558 else 560)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 559 else (if i.val < 562 then
      583 else 582)) else (if i.val < 564 then 584 else (if i.val < 565 then 585 else 587)))
      else (if i.val < 569 then (if i.val < 567 then 586 else (if i.val < 568 then 588 else
      589)) else (if i.val < 570 then 549 else (if i.val < 571 then 550 else 551)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 553 else (if i.val < 574 then
      552 else 575)) else (if i.val < 576 then 574 else (if i.val < 577 then 576 else 577)))
      else (if i.val < 581 then (if i.val < 579 then 579 else (if i.val < 580 then 578 else
      580)) else (if i.val < 583 then (if i.val < 582 then 581 else 562) else (if i.val < 584
      then 561 else 563))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 564 else (if i.val < 587 then 566 else 565)) else (if i.val < 589
      then 567 else (if i.val < 590 then 568 else 592))) else (if i.val < 594 then (if i.val <
      592 then 591 else (if i.val < 593 then 590 else 593)) else (if i.val < 596 then (if i.val
      < 595 then 596 else 595) else (if i.val < 597 then 594 else 597)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 600 else (if i.val < 600 then 599 else
      598)) else (if i.val < 602 then 601 else (if i.val < 603 then 602 else 605))) else (if
      i.val < 607 then (if i.val < 605 then 604 else (if i.val < 606 then 603 else 630)) else
      (if i.val < 609 then (if i.val < 608 then 632 else 631) else (if i.val < 610 then 633 else
      634)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 635 else (if
      i.val < 613 then 637 else 636)) else (if i.val < 615 then 614 else (if i.val < 616 then
      616 else 615))) else (if i.val < 620 then (if i.val < 618 then 617 else (if i.val < 619
      then 618 else 619)) else (if i.val < 621 then 621 else (if i.val < 622 then 620 else
      647)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 646 else (if
      i.val < 625 then 648 else 649)) else (if i.val < 627 then 651 else (if i.val < 628 then
      650 else 652))) else (if i.val < 632 then (if i.val < 630 then 653 else (if i.val < 631
      then 606 else 608)) else (if i.val < 634 then (if i.val < 633 then 607 else 609) else (if
      i.val < 635 then 610 else 611))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 613 else (if i.val < 638 then 612 else 639)) else
      (if i.val < 640 then 638 else (if i.val < 641 then 640 else 641))) else (if i.val < 645
      then (if i.val < 643 then 643 else (if i.val < 644 then 642 else 644)) else (if i.val <
      647 then (if i.val < 646 then 645 else 623) else (if i.val < 648 then 622 else 624))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 625 else (if i.val <
      651 then 627 else 626)) else (if i.val < 653 then 628 else (if i.val < 654 then 629 else
      656))) else (if i.val < 658 then (if i.val < 656 then 655 else (if i.val < 657 then 654
      else 657)) else (if i.val < 660 then (if i.val < 659 then 660 else 659) else (if i.val <
      661 then 658 else 661)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 728 else (if i.val < 664 then 727 else
      702)) else (if i.val < 666 then 729 else (if i.val < 667 then 730 else 733))) else (if
      i.val < 671 then (if i.val < 669 then 734 else (if i.val < 670 then 731 else 732)) else
      (if i.val < 672 then 735 else (if i.val < 673 then 736 else 737)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 738 else (if i.val < 676 then 741 else
      742)) else (if i.val < 678 then 739 else (if i.val < 679 then 740 else 743))) else (if
      i.val < 683 then (if i.val < 681 then 744 else (if i.val < 682 then 682 else 681)) else
      (if i.val < 685 then (if i.val < 684 then 683 else 684) else (if i.val < 686 then 685 else
      688))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 689 else (if i.val < 689 then 686 else 687)) else (if i.val < 691 then 690 else
      (if i.val < 692 then 691 else 692))) else (if i.val < 696 then (if i.val < 694 then 693
      else (if i.val < 695 then 696 else 697)) else (if i.val < 698 then (if i.val < 697 then
      694 else 695) else (if i.val < 699 then 698 else 699)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 771 else (if i.val < 702 then 772 else 664)) else
      (if i.val < 704 then 773 else (if i.val < 705 then 774 else 775))) else (if i.val < 709
      then (if i.val < 707 then 776 else (if i.val < 708 then 777 else 778)) else (if i.val <
      711 then (if i.val < 710 then 779 else 780) else (if i.val < 712 then 781 else 782)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 783 else (if i.val < 715 then 784 else 785))
      else (if i.val < 717 then 786 else (if i.val < 718 then 787 else 788))) else (if i.val <
      722 then (if i.val < 720 then 789 else (if i.val < 721 then 790 else 791)) else (if i.val
      < 723 then 792 else (if i.val < 724 then 793 else 794)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 795 else (if i.val < 727 then 796 else 663)) else
      (if i.val < 729 then 662 else (if i.val < 730 then 665 else 666))) else (if i.val < 734
      then (if i.val < 732 then 669 else (if i.val < 733 then 670 else 667)) else (if i.val <
      736 then (if i.val < 735 then 668 else 671) else (if i.val < 737 then 672 else 673)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      674 else (if i.val < 740 then 677 else 678)) else (if i.val < 742 then 675 else (if i.val
      < 743 then 676 else 679))) else (if i.val < 747 then (if i.val < 745 then 680 else (if
      i.val < 746 then 745 else 746)) else (if i.val < 749 then (if i.val < 748 then 747 else
      748) else (if i.val < 750 then 749 else 750)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 751 else (if i.val < 753 then 752 else 753)) else (if i.val <
      755 then 754 else (if i.val < 756 then 755 else 756))) else (if i.val < 760 then (if i.val
      < 758 then 757 else (if i.val < 759 then 758 else 759)) else (if i.val < 762 then (if
      i.val < 761 then 760 else 761) else (if i.val < 763 then 762 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 700 else 701)) else (if i.val < 774 then 703 else (if i.val < 775
      then 704 else 705)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      706 else (if i.val < 778 then 707 else 708)) else (if i.val < 780 then 709 else (if i.val
      < 781 then 710 else 711))) else (if i.val < 785 then (if i.val < 783 then 712 else (if
      i.val < 784 then 713 else 714)) else (if i.val < 787 then (if i.val < 786 then 715 else
      716) else (if i.val < 788 then 717 else 718))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 719 else (if i.val < 791 then 720 else
      721)) else (if i.val < 793 then 722 else (if i.val < 794 then 723 else 724))) else (if
      i.val < 798 then (if i.val < 796 then 725 else (if i.val < 797 then 726 else 797)) else
      (if i.val < 800 then (if i.val < 799 then 798 else 799) else (if i.val < 801 then 800 else
      801)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 802 else (if
      i.val < 804 then 803 else 804)) else (if i.val < 806 then 809 else (if i.val < 807 then
      806 else 812))) else (if i.val < 811 then (if i.val < 809 then 813 else (if i.val < 810
      then 805 else 810)) else (if i.val < 813 then (if i.val < 812 then 811 else 807) else (if
      i.val < 814 then 808 else 814)))))))))))
  invFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 16 else (if i.val < 2 then 18 else 15)) else (if i.val < 4 then 17 else (if i.val <
      5 then 6 else 5))) else (if i.val < 9 then (if i.val < 7 then 4 else (if i.val < 8 then 31
      else 32)) else (if i.val < 10 then 33 else (if i.val < 11 then 35 else 34)))) else (if
      i.val < 18 then (if i.val < 15 then (if i.val < 13 then 36 else (if i.val < 14 then 37
      else 38)) else (if i.val < 16 then 2 else (if i.val < 17 then 0 else 3))) else (if i.val <
      21 then (if i.val < 19 then 1 else (if i.val < 20 then 19 else 20)) else (if i.val < 23
      then (if i.val < 22 then 21 else 22) else (if i.val < 24 then 25 else 26))))) else (if
      i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 23 else (if
      i.val < 27 then 24 else 27)) else (if i.val < 29 then 28 else (if i.val < 30 then 29 else
      30))) else (if i.val < 34 then (if i.val < 32 then 7 else (if i.val < 33 then 8 else 9))
      else (if i.val < 35 then 11 else (if i.val < 36 then 10 else 12)))) else (if i.val < 43
      then (if i.val < 40 then (if i.val < 38 then 13 else (if i.val < 39 then 14 else 41)) else
      (if i.val < 41 then 40 else (if i.val < 42 then 39 else 42))) else (if i.val < 46 then (if
      i.val < 44 then 43 else (if i.val < 45 then 46 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 44 else 47) else (if i.val < 49 then 77 else 78)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 75
      else (if i.val < 52 then 76 else 69)) else (if i.val < 54 then 68 else (if i.val < 55 then
      80 else 79))) else (if i.val < 59 then (if i.val < 57 then 81 else (if i.val < 58 then 59
      else 60)) else (if i.val < 60 then 57 else (if i.val < 61 then 58 else 61)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 62 else (if i.val < 64 then 63
      else 93)) else (if i.val < 66 then 94 else (if i.val < 67 then 95 else 96))) else (if
      i.val < 71 then (if i.val < 69 then 53 else (if i.val < 70 then 52 else 97)) else (if
      i.val < 73 then (if i.val < 72 then 99 else 98) else (if i.val < 74 then 100 else 101)))))
      else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then 50
      else (if i.val < 77 then 51 else 48)) else (if i.val < 79 then 49 else (if i.val < 80 then
      55 else 54))) else (if i.val < 84 then (if i.val < 82 then 56 else (if i.val < 83 then 82
      else 83)) else (if i.val < 86 then (if i.val < 85 then 84 else 85) else (if i.val < 87
      then 86 else 87)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then 88
      else (if i.val < 90 then 90 else 89)) else (if i.val < 92 then 91 else (if i.val < 93 then
      92 else 64))) else (if i.val < 97 then (if i.val < 95 then 65 else (if i.val < 96 then 66
      else 67)) else (if i.val < 99 then (if i.val < 98 then 70 else 72) else (if i.val < 100
      then 71 else 73))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then
      (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 74 else (if i.val < 103
      then 104 else 103)) else (if i.val < 105 then 102 else (if i.val < 106 then 105 else
      116))) else (if i.val < 110 then (if i.val < 108 then 115 else (if i.val < 109 then 114
      else 110)) else (if i.val < 111 then 109 else (if i.val < 112 then 111 else 119)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 120 else (if i.val < 115
      then 108 else 107)) else (if i.val < 117 then 106 else (if i.val < 118 then 117 else
      118))) else (if i.val < 122 then (if i.val < 120 then 112 else (if i.val < 121 then 113
      else 183)) else (if i.val < 124 then (if i.val < 123 then 182 else 184) else (if i.val <
      125 then 185 else 186))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 187 else (if i.val < 128 then 189 else 188)) else (if i.val <
      130 then 190 else (if i.val < 131 then 199 else 200))) else (if i.val < 135 then (if i.val
      < 133 then 196 else (if i.val < 134 then 197 else 198)) else (if i.val < 137 then (if
      i.val < 136 then 193 else 194) else (if i.val < 138 then 195 else 191)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 192 else (if i.val < 141 then 141 else
      140)) else (if i.val < 143 then 142 else (if i.val < 144 then 143 else 145))) else (if
      i.val < 148 then (if i.val < 146 then 144 else (if i.val < 147 then 146 else 153)) else
      (if i.val < 150 then (if i.val < 149 then 154 else 151) else (if i.val < 151 then 152 else
      149)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 150 else (if i.val < 154 then 147 else 148)) else (if i.val
      < 156 then 233 else (if i.val < 157 then 234 else 235))) else (if i.val < 161 then (if
      i.val < 159 then 236 else (if i.val < 160 then 237 else 238)) else (if i.val < 162 then
      239 else (if i.val < 163 then 240 else 241)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 242 else (if i.val < 166 then 243 else 244)) else (if i.val <
      168 then 245 else (if i.val < 169 then 246 else 247))) else (if i.val < 173 then (if i.val
      < 171 then 249 else (if i.val < 172 then 248 else 250)) else (if i.val < 175 then (if
      i.val < 174 then 251 else 252) else (if i.val < 176 then 253 else 254))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 255 else (if
      i.val < 179 then 256 else 257)) else (if i.val < 181 then 258 else (if i.val < 182 then
      259 else 122))) else (if i.val < 186 then (if i.val < 184 then 121 else (if i.val < 185
      then 123 else 124)) else (if i.val < 188 then (if i.val < 187 then 125 else 126) else (if
      i.val < 189 then 128 else 127)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 129 else (if i.val < 192 then 138 else 139)) else (if i.val < 194 then 135 else
      (if i.val < 195 then 136 else 137))) else (if i.val < 199 then (if i.val < 197 then 132
      else (if i.val < 198 then 133 else 134)) else (if i.val < 201 then (if i.val < 200 then
      130 else 131) else (if i.val < 202 then 201 else 202)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 203 else (if i.val < 205 then 204 else 205)) else (if
      i.val < 207 then 206 else (if i.val < 208 then 207 else 208))) else (if i.val < 212 then
      (if i.val < 210 then 209 else (if i.val < 211 then 210 else 211)) else (if i.val < 213
      then 212 else (if i.val < 214 then 213 else 214)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 215 else (if i.val < 217 then 216 else 217)) else (if i.val
      < 219 then 218 else (if i.val < 220 then 219 else 221))) else (if i.val < 224 then (if
      i.val < 222 then 220 else (if i.val < 223 then 222 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 227 else 226))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 228 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 155))) else (if i.val < 237 then (if i.val < 235 then 156 else (if i.val <
      236 then 157 else 158)) else (if i.val < 239 then (if i.val < 238 then 159 else 160) else
      (if i.val < 240 then 161 else 162)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 163 else (if i.val < 243 then 164 else 165)) else (if i.val < 245 then
      166 else (if i.val < 246 then 167 else 168))) else (if i.val < 250 then (if i.val < 248
      then 169 else (if i.val < 249 then 171 else 170)) else (if i.val < 252 then (if i.val <
      251 then 172 else 173) else (if i.val < 253 then 174 else 175)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      176 else (if i.val < 256 then 177 else 178)) else (if i.val < 258 then 179 else (if i.val
      < 259 then 180 else 181))) else (if i.val < 263 then (if i.val < 261 then 262 else (if
      i.val < 262 then 261 else 260)) else (if i.val < 264 then 263 else (if i.val < 265 then
      264 else 265)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 267
      else (if i.val < 268 then 266 else 268)) else (if i.val < 270 then 269 else (if i.val <
      271 then 270 else 271))) else (if i.val < 275 then (if i.val < 273 then 274 else (if i.val
      < 274 then 273 else 272)) else (if i.val < 277 then (if i.val < 276 then 275 else 276)
      else (if i.val < 278 then 295 else 296))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 297 else (if i.val < 281 then 299 else 298))
      else (if i.val < 283 then 283 else (if i.val < 284 then 282 else 284))) else (if i.val <
      288 then (if i.val < 286 then 285 else (if i.val < 287 then 287 else 286)) else (if i.val
      < 290 then (if i.val < 289 then 308 else 309) else (if i.val < 291 then 310 else 312))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 311 else (if i.val <
      294 then 313 else 314)) else (if i.val < 296 then 277 else (if i.val < 297 then 278 else
      279))) else (if i.val < 301 then (if i.val < 299 then 281 else (if i.val < 300 then 280
      else 301)) else (if i.val < 303 then (if i.val < 302 then 300 else 302) else (if i.val <
      304 then 303 else 305))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 304 else (if i.val
      < 307 then 306 else 307)) else (if i.val < 309 then 288 else (if i.val < 310 then 289 else
      290))) else (if i.val < 314 then (if i.val < 312 then 292 else (if i.val < 313 then 291
      else 293)) else (if i.val < 315 then 294 else (if i.val < 316 then 317 else 316)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 315 else (if i.val < 319
      then 318 else 321)) else (if i.val < 321 then 320 else (if i.val < 322 then 319 else
      322))) else (if i.val < 326 then (if i.val < 324 then 333 else (if i.val < 325 then 335
      else 334)) else (if i.val < 328 then (if i.val < 327 then 326 else 328) else (if i.val <
      329 then 327 else 340))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 342 else (if i.val < 332 then 341 else 343)) else (if i.val <
      334 then 323 else (if i.val < 335 then 325 else 324))) else (if i.val < 339 then (if i.val
      < 337 then 336 else (if i.val < 338 then 338 else 337)) else (if i.val < 341 then (if
      i.val < 340 then 339 else 329) else (if i.val < 342 then 331 else 330)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 332 else (if i.val < 345 then 376 else
      375)) else (if i.val < 347 then 374 else (if i.val < 348 then 363 else 361))) else (if
      i.val < 352 then (if i.val < 350 then 362 else (if i.val < 351 then 353 else 351)) else
      (if i.val < 354 then (if i.val < 353 then 352 else 350) else (if i.val < 355 then 373 else
      371)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 372 else (if i.val < 358 then 370 else 368)) else (if i.val
      < 360 then 369 else (if i.val < 361 then 367 else 348))) else (if i.val < 365 then (if
      i.val < 363 then 349 else (if i.val < 364 then 347 else 366)) else (if i.val < 366 then
      365 else (if i.val < 367 then 364 else 360)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 358 else (if i.val < 370 then 359 else 357)) else (if i.val <
      372 then 355 else (if i.val < 373 then 356 else 354))) else (if i.val < 377 then (if i.val
      < 375 then 346 else (if i.val < 376 then 345 else 344)) else (if i.val < 379 then (if
      i.val < 378 then 401 else 402) else (if i.val < 380 then 399 else 400))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 395 else (if
      i.val < 383 then 396 else 403)) else (if i.val < 385 then 386 else (if i.val < 386 then
      387 else 384))) else (if i.val < 390 then (if i.val < 388 then 385 else (if i.val < 389
      then 388 else 389)) else (if i.val < 392 then (if i.val < 391 then 390 else 410) else (if
      i.val < 393 then 411 else 412)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 413 else (if i.val < 396 then 381 else 382)) else (if i.val < 398 then 414 else
      (if i.val < 399 then 415 else 379))) else (if i.val < 403 then (if i.val < 401 then 380
      else (if i.val < 402 then 377 else 378)) else (if i.val < 405 then (if i.val < 404 then
      383 else 404) else (if i.val < 406 then 405 else 406))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 407 else (if i.val < 409 then
      408 else 409)) else (if i.val < 411 then 391 else (if i.val < 412 then 392 else 393)))
      else (if i.val < 416 then (if i.val < 414 then 394 else (if i.val < 415 then 397 else
      398)) else (if i.val < 417 then 416 else (if i.val < 418 then 450 else 453)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 454 else (if i.val < 421 then
      451 else 452)) else (if i.val < 423 then 455 else (if i.val < 424 then 456 else 458)))
      else (if i.val < 428 then (if i.val < 426 then 457 else (if i.val < 427 then 459 else
      427)) else (if i.val < 430 then (if i.val < 429 then 430 else 431) else (if i.val < 431
      then 428 else 429))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 432 else (if i.val < 434 then 433 else 435)) else (if i.val < 436
      then 434 else (if i.val < 437 then 436 else 473))) else (if i.val < 441 then (if i.val <
      439 then 474 else (if i.val < 440 then 475 else 476)) else (if i.val < 443 then (if i.val
      < 442 then 477 else 478) else (if i.val < 444 then 479 else 480)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 481 else (if i.val < 447 then 482 else
      483)) else (if i.val < 449 then 484 else (if i.val < 450 then 485 else 417))) else (if
      i.val < 454 then (if i.val < 452 then 420 else (if i.val < 453 then 421 else 418)) else
      (if i.val < 456 then (if i.val < 455 then 419 else 422) else (if i.val < 457 then 423 else
      425)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 424 else (if i.val < 460 then 426 else 460)) else (if i.val
      < 462 then 461 else (if i.val < 463 then 462 else 463))) else (if i.val < 467 then (if
      i.val < 465 then 464 else (if i.val < 466 then 465 else 466)) else (if i.val < 468 then
      467 else (if i.val < 469 then 468 else 469)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 437 else (if i.val < 475 then 438 else 439))) else (if i.val < 479 then (if i.val
      < 477 then 440 else (if i.val < 478 then 441 else 442)) else (if i.val < 481 then (if
      i.val < 480 then 443 else 444) else (if i.val < 482 then 445 else 446))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 447 else (if
      i.val < 485 then 448 else 449)) else (if i.val < 487 then 486 else (if i.val < 488 then
      487 else 488))) else (if i.val < 492 then (if i.val < 490 then 493 else (if i.val < 491
      then 490 else 496)) else (if i.val < 494 then (if i.val < 493 then 497 else 489) else (if
      i.val < 495 then 494 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 491 else (if i.val < 498 then 492 else 498)) else (if i.val < 500 then 515 else
      (if i.val < 501 then 517 else 516))) else (if i.val < 505 then (if i.val < 503 then 518
      else (if i.val < 504 then 503 else 505)) else (if i.val < 507 then (if i.val < 506 then
      504 else 529) else (if i.val < 508 then 530 else 531))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 532 else (if i.val < 511 then 534 else 533)) else (if i.val < 513 then 535 else
      (if i.val < 514 then 536 else 537))) else (if i.val < 518 then (if i.val < 516 then 499
      else (if i.val < 517 then 501 else 500)) else (if i.val < 519 then 502 else (if i.val <
      520 then 519 else 520)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 521 else (if i.val < 523 then 522 else 523)) else (if i.val < 525 then 525 else (if
      i.val < 526 then 524 else 526))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 506)) else (if i.val < 532 then (if i.val < 531 then 507
      else 508) else (if i.val < 533 then 509 else 511))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 510 else (if i.val < 536 then 512
      else 513)) else (if i.val < 538 then 514 else (if i.val < 539 then 538 else 541))) else
      (if i.val < 543 then (if i.val < 541 then 540 else (if i.val < 542 then 539 else 542))
      else (if i.val < 545 then (if i.val < 544 then 543 else 546) else (if i.val < 546 then 545
      else 544)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 547 else
      (if i.val < 549 then 548 else 569)) else (if i.val < 551 then 570 else (if i.val < 552
      then 571 else 573))) else (if i.val < 556 then (if i.val < 554 then 572 else (if i.val <
      555 then 555 else 554)) else (if i.val < 558 then (if i.val < 557 then 556 else 557) else
      (if i.val < 559 then 558 else 560)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 559 else (if i.val < 562 then
      583 else 582)) else (if i.val < 564 then 584 else (if i.val < 565 then 585 else 587)))
      else (if i.val < 569 then (if i.val < 567 then 586 else (if i.val < 568 then 588 else
      589)) else (if i.val < 570 then 549 else (if i.val < 571 then 550 else 551)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 553 else (if i.val < 574 then
      552 else 575)) else (if i.val < 576 then 574 else (if i.val < 577 then 576 else 577)))
      else (if i.val < 581 then (if i.val < 579 then 579 else (if i.val < 580 then 578 else
      580)) else (if i.val < 583 then (if i.val < 582 then 581 else 562) else (if i.val < 584
      then 561 else 563))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 564 else (if i.val < 587 then 566 else 565)) else (if i.val < 589
      then 567 else (if i.val < 590 then 568 else 592))) else (if i.val < 594 then (if i.val <
      592 then 591 else (if i.val < 593 then 590 else 593)) else (if i.val < 596 then (if i.val
      < 595 then 596 else 595) else (if i.val < 597 then 594 else 597)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 600 else (if i.val < 600 then 599 else
      598)) else (if i.val < 602 then 601 else (if i.val < 603 then 602 else 605))) else (if
      i.val < 607 then (if i.val < 605 then 604 else (if i.val < 606 then 603 else 630)) else
      (if i.val < 609 then (if i.val < 608 then 632 else 631) else (if i.val < 610 then 633 else
      634)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 635 else (if
      i.val < 613 then 637 else 636)) else (if i.val < 615 then 614 else (if i.val < 616 then
      616 else 615))) else (if i.val < 620 then (if i.val < 618 then 617 else (if i.val < 619
      then 618 else 619)) else (if i.val < 621 then 621 else (if i.val < 622 then 620 else
      647)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 646 else (if
      i.val < 625 then 648 else 649)) else (if i.val < 627 then 651 else (if i.val < 628 then
      650 else 652))) else (if i.val < 632 then (if i.val < 630 then 653 else (if i.val < 631
      then 606 else 608)) else (if i.val < 634 then (if i.val < 633 then 607 else 609) else (if
      i.val < 635 then 610 else 611))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 613 else (if i.val < 638 then 612 else 639)) else
      (if i.val < 640 then 638 else (if i.val < 641 then 640 else 641))) else (if i.val < 645
      then (if i.val < 643 then 643 else (if i.val < 644 then 642 else 644)) else (if i.val <
      647 then (if i.val < 646 then 645 else 623) else (if i.val < 648 then 622 else 624))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 625 else (if i.val <
      651 then 627 else 626)) else (if i.val < 653 then 628 else (if i.val < 654 then 629 else
      656))) else (if i.val < 658 then (if i.val < 656 then 655 else (if i.val < 657 then 654
      else 657)) else (if i.val < 660 then (if i.val < 659 then 660 else 659) else (if i.val <
      661 then 658 else 661)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 728 else (if i.val < 664 then 727 else
      702)) else (if i.val < 666 then 729 else (if i.val < 667 then 730 else 733))) else (if
      i.val < 671 then (if i.val < 669 then 734 else (if i.val < 670 then 731 else 732)) else
      (if i.val < 672 then 735 else (if i.val < 673 then 736 else 737)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 738 else (if i.val < 676 then 741 else
      742)) else (if i.val < 678 then 739 else (if i.val < 679 then 740 else 743))) else (if
      i.val < 683 then (if i.val < 681 then 744 else (if i.val < 682 then 682 else 681)) else
      (if i.val < 685 then (if i.val < 684 then 683 else 684) else (if i.val < 686 then 685 else
      688))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 689 else (if i.val < 689 then 686 else 687)) else (if i.val < 691 then 690 else
      (if i.val < 692 then 691 else 692))) else (if i.val < 696 then (if i.val < 694 then 693
      else (if i.val < 695 then 696 else 697)) else (if i.val < 698 then (if i.val < 697 then
      694 else 695) else (if i.val < 699 then 698 else 699)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 771 else (if i.val < 702 then 772 else 664)) else
      (if i.val < 704 then 773 else (if i.val < 705 then 774 else 775))) else (if i.val < 709
      then (if i.val < 707 then 776 else (if i.val < 708 then 777 else 778)) else (if i.val <
      711 then (if i.val < 710 then 779 else 780) else (if i.val < 712 then 781 else 782)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 783 else (if i.val < 715 then 784 else 785))
      else (if i.val < 717 then 786 else (if i.val < 718 then 787 else 788))) else (if i.val <
      722 then (if i.val < 720 then 789 else (if i.val < 721 then 790 else 791)) else (if i.val
      < 723 then 792 else (if i.val < 724 then 793 else 794)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 795 else (if i.val < 727 then 796 else 663)) else
      (if i.val < 729 then 662 else (if i.val < 730 then 665 else 666))) else (if i.val < 734
      then (if i.val < 732 then 669 else (if i.val < 733 then 670 else 667)) else (if i.val <
      736 then (if i.val < 735 then 668 else 671) else (if i.val < 737 then 672 else 673)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      674 else (if i.val < 740 then 677 else 678)) else (if i.val < 742 then 675 else (if i.val
      < 743 then 676 else 679))) else (if i.val < 747 then (if i.val < 745 then 680 else (if
      i.val < 746 then 745 else 746)) else (if i.val < 749 then (if i.val < 748 then 747 else
      748) else (if i.val < 750 then 749 else 750)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 751 else (if i.val < 753 then 752 else 753)) else (if i.val <
      755 then 754 else (if i.val < 756 then 755 else 756))) else (if i.val < 760 then (if i.val
      < 758 then 757 else (if i.val < 759 then 758 else 759)) else (if i.val < 762 then (if
      i.val < 761 then 760 else 761) else (if i.val < 763 then 762 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 700 else 701)) else (if i.val < 774 then 703 else (if i.val < 775
      then 704 else 705)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      706 else (if i.val < 778 then 707 else 708)) else (if i.val < 780 then 709 else (if i.val
      < 781 then 710 else 711))) else (if i.val < 785 then (if i.val < 783 then 712 else (if
      i.val < 784 then 713 else 714)) else (if i.val < 787 then (if i.val < 786 then 715 else
      716) else (if i.val < 788 then 717 else 718))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 719 else (if i.val < 791 then 720 else
      721)) else (if i.val < 793 then 722 else (if i.val < 794 then 723 else 724))) else (if
      i.val < 798 then (if i.val < 796 then 725 else (if i.val < 797 then 726 else 797)) else
      (if i.val < 800 then (if i.val < 799 then 798 else 799) else (if i.val < 801 then 800 else
      801)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 802 else (if
      i.val < 804 then 803 else 804)) else (if i.val < 806 then 809 else (if i.val < 807 then
      806 else 812))) else (if i.val < 811 then (if i.val < 809 then 813 else (if i.val < 810
      then 805 else 810)) else (if i.val < 813 then (if i.val < 812 then 811 else 807) else (if
      i.val < 814 then 808 else 814)))))))))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed vertex, edge and branch bijections for this frame permutation. -/
def hint2 : Fin 815 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
    (if i.val < 25 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 37 then ⟨[0, 1], [0], [false]⟩
    else (if i.val < 43 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 46 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 48 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))))) else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53
    then (if i.val < 51 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 52 then ⟨[0,
    1, 2], [0, 1], [false, false]⟩ else ⟨[1, 0, 2], [1, 0], [false, false]⟩)) else (if i.val <
    54 then ⟨[1, 0, 2], [1, 0], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else
    ⟨[0, 1, 2], [0, 1], [false, false]⟩) else (if i.val < 68 then ⟨[0, 1, 2], [0, 1], [false,
    false]⟩ else (if i.val < 71 then (if i.val < 69 then ⟨[1, 0, 2], [1, 0], [false, false]⟩
    else (if i.val < 70 then ⟨[1, 0, 2], [1, 0], [false, false]⟩ else ⟨[0, 1, 2], [0, 1],
    [false, false]⟩)) else ⟨[0, 1, 2], [0, 1], [false, false]⟩))) else ⟨[0, 1, 2], [0, 1],
    [false, false]⟩)) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if
    i.val < 107 then (if i.val < 104 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val <
    105 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 106 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩))) else (if i.val <
    110 then (if i.val < 108 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if
    i.val < 109 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1,
    2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else
    (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 115 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false,
    false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1,
    2], [false, false, false]⟩) else (if i.val < 122 then (if i.val < 120 then ⟨[0, 1, 2, 3],
    [0, 1, 2], [false, false, false]⟩ else (if i.val < 121 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else ⟨[0, 1, 2], [0, 1],
    [false, false]⟩))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129 then ⟨[0,
    1, 2], [0, 1], [false, false]⟩ else (if i.val < 130 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else ⟨[0, 2, 1], [0, 1], [false, true]⟩)) else ⟨[0, 2, 1], [0, 1], [false, true]⟩) else (if
    i.val < 145 then (if i.val < 142 then (if i.val < 140 then ⟨[0, 2, 1], [0, 1], [false,
    true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)
    else (if i.val < 148 then (if i.val < 146 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if
    i.val < 147 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 2, 1], [0, 1], [false,
    true]⟩)) else ⟨[0, 2, 1], [0, 1], [false, true]⟩)))) else (if i.val < 177 then (if i.val <
    164 then (if i.val < 158 then (if i.val < 155 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else
    ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1,
    2], [0, 1], [false, false]⟩) else (if i.val < 190 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else (if i.val < 196 then (if i.val < 193 then (if i.val < 191 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[0, 2, 1], [0, 1], [false, true]⟩) else ⟨[0, 2, 1], [0, 1], [false,
    true]⟩) else (if i.val < 199 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else (if i.val < 201
    then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩))))))) else
    (if i.val < 305 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 356 then (if i.val
    < 330 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 343 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else (if i.val < 349 then (if i.val < 346 then (if i.val < 344 then ⟨[0, 1,
    2], [0, 1], [false, false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩) else ⟨[2, 1, 0], [1, 0],
    [true, true]⟩) else ⟨[2, 1, 0], [1, 0], [true, true]⟩))) else (if i.val < 381 then (if i.val
    < 368 then (if i.val < 362 then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else (if i.val < 365 then
    ⟨[2, 1, 0], [1, 0], [true, true]⟩ else (if i.val < 366 then ⟨[0, 1, 2], [0, 1], [false,
    false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩))) else (if i.val < 374 then ⟨[2, 1, 0], [1,
    0], [true, true]⟩ else (if i.val < 377 then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else ⟨[0, 1,
    2, 3], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 394 then (if i.val < 387 then
    (if i.val < 384 then (if i.val < 382 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false, false]⟩
    else (if i.val < 383 then ⟨[1, 0, 3, 2], [1, 0, 2], [false, false, true]⟩ else ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 400 then
    (if i.val < 397 then (if i.val < 395 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩
    else (if i.val < 396 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false, false]⟩ else ⟨[1, 0, 3,
    2], [1, 0, 2], [false, false, true]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)))))) else (if i.val < 611
    then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 425 then ⟨[0, 1, 2, 3],
    [0, 1, 2], [false, false, false]⟩ else (if i.val < 428 then (if i.val < 426 then ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 427 then ⟨[0, 3, 2, 1], [0, 2, 1],
    [false, true, true]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 445 then (if i.val < 438 then (if
    i.val < 435 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 436 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 437 then ⟨[0, 3, 2, 1],
    [0, 2, 1], [false, true, true]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)))
    else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩)) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then
    (if i.val < 461 then (if i.val < 459 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩
    else (if i.val < 460 then ⟨[0, 3, 2, 1], [0, 2, 1], [false, true, true]⟩ else ⟨[0, 1, 2, 3],
    [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)
    else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩) else (if i.val < 496 then (if i.val < 489 then ⟨[0, 1, 2, 3], [0, 1,
    2], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else (if i.val < 502
    then (if i.val < 499 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 1], [0, 1], [false,
    false]⟩) else ⟨[0, 1], [0, 1], [false, false]⟩)))) else ⟨[0, 1], [0, 1], [false, false]⟩)
    else (if i.val < 713 then (if i.val < 662 then ⟨[0, 1], [0, 1], [false, false]⟩ else (if
    i.val < 687 then (if i.val < 674 then (if i.val < 668 then (if i.val < 665 then (if i.val <
    663 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 664 then ⟨[0, 1, 2],
    [0, 1, 2], [false, false, false]⟩ else ⟨[1, 0, 2], [0, 2, 1], [false, false, false]⟩)) else
    ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1, 2], [0, 1, 2], [false, false,
    false]⟩) else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩) else (if i.val < 700 then ⟨[0,
    1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 706 then (if i.val < 703 then (if
    i.val < 701 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 702 then
    ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 0, 2], [0, 2, 1], [false, false,
    false]⟩)) else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1, 2], [0, 1, 2],
    [false, false, false]⟩)))) else (if i.val < 764 then ⟨[0, 1, 2], [0, 1, 2], [false, false,
    false]⟩ else (if i.val < 789 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if
    i.val < 802 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 808 then (if
    i.val < 805 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1], [0, 1, 2],
    [false, false, false]⟩) else ⟨[0, 1], [0, 1, 2], [false, false, false]⟩))))))))

/-- The kernel checks the supplied bijections without repeating permutation search. -/
theorem hints_valid2 : ∀ i, (hint2 i).check ((L24Graphs.graph i).relabel labels2)
    (L24Graphs.graph (destination2 i)) = true := by
  decide +kernel

/-- Every column is transported as a full decorated labelled graph. -/
theorem covered2 : ∀ i, ((L24Graphs.graph i).relabel labels2).isomorphic?
    (L24Graphs.graph (destination2 i)) = true := by
  intro i
  exact (hint2 i).check_sound _ _ (hints_valid2 i)

/-- The 3-th permutation of the three free markings; old labels map covariantly. -/
def labels3 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 0, 2]
  invFun := ![2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A candidate bijection of the held frame columns. -/
def destination3 : Equiv.Perm (Fin 815) where
  toFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 20 else (if i.val < 2 then 22 else 19)) else (if i.val < 4 then 21 else (if i.val <
      5 then 9 else 8))) else (if i.val < 9 then (if i.val < 7 then 7 else (if i.val < 8 then 33
      else 32)) else (if i.val < 10 then 31 else (if i.val < 11 then 40 else 39)))) else (if
      i.val < 18 then (if i.val < 15 then (if i.val < 13 then 41 else (if i.val < 14 then 42
      else 43)) else (if i.val < 16 then 2 else (if i.val < 17 then 0 else 3))) else (if i.val <
      21 then (if i.val < 19 then 1 else (if i.val < 20 then 15 else 16)) else (if i.val < 23
      then (if i.val < 22 then 17 else 18) else (if i.val < 24 then 27 else 28))))) else (if
      i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 23 else (if
      i.val < 27 then 24 else 25)) else (if i.val < 29 then 26 else (if i.val < 30 then 29 else
      30))) else (if i.val < 34 then (if i.val < 32 then 4 else (if i.val < 33 then 5 else 6))
      else (if i.val < 35 then 12 else (if i.val < 36 then 10 else 11)))) else (if i.val < 43
      then (if i.val < 40 then (if i.val < 38 then 13 else (if i.val < 39 then 14 else 36)) else
      (if i.val < 41 then 35 else (if i.val < 42 then 34 else 37))) else (if i.val < 46 then (if
      i.val < 44 then 38 else (if i.val < 45 then 47 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 44 else 46) else (if i.val < 49 then 84 else 85)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 82
      else (if i.val < 52 then 83 else 62)) else (if i.val < 54 then 61 else (if i.val < 55 then
      87 else 86))) else (if i.val < 59 then (if i.val < 57 then 88 else (if i.val < 58 then 66
      else 67)) else (if i.val < 60 then 64 else (if i.val < 61 then 65 else 68)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 69 else (if i.val < 64 then 70
      else 95)) else (if i.val < 66 then 96 else (if i.val < 67 then 93 else 94))) else (if
      i.val < 71 then (if i.val < 69 then 53 else (if i.val < 70 then 52 else 97)) else (if
      i.val < 73 then (if i.val < 72 then 103 else 102) else (if i.val < 74 then 104 else
      105))))) else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76
      then 50 else (if i.val < 77 then 51 else 48)) else (if i.val < 79 then 49 else (if i.val <
      80 then 55 else 54))) else (if i.val < 84 then (if i.val < 82 then 56 else (if i.val < 83
      then 75 else 76)) else (if i.val < 86 then (if i.val < 85 then 77 else 78) else (if i.val
      < 87 then 79 else 80)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then
      81 else (if i.val < 90 then 91 else 89)) else (if i.val < 92 then 90 else (if i.val < 93
      then 92 else 57))) else (if i.val < 97 then (if i.val < 95 then 58 else (if i.val < 96
      then 59 else 60)) else (if i.val < 99 then (if i.val < 98 then 63 else 73) else (if i.val
      < 100 then 71 else 72))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val <
      113 then (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 74 else (if i.val
      < 103 then 100 else 99)) else (if i.val < 105 then 98 else (if i.val < 106 then 101 else
      118))) else (if i.val < 110 then (if i.val < 108 then 117 else (if i.val < 109 then 111
      else 113)) else (if i.val < 111 then 112 else (if i.val < 112 then 114 else 120)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 119 else (if i.val < 115
      then 108 else 107)) else (if i.val < 117 then 106 else (if i.val < 118 then 115 else
      116))) else (if i.val < 122 then (if i.val < 120 then 109 else (if i.val < 121 then 110
      else 202)) else (if i.val < 124 then (if i.val < 123 then 201 else 203) else (if i.val <
      125 then 204 else 205))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 206 else (if i.val < 128 then 208 else 207)) else (if i.val <
      130 then 209 else (if i.val < 131 then 218 else 219))) else (if i.val < 135 then (if i.val
      < 133 then 215 else (if i.val < 134 then 216 else 217)) else (if i.val < 137 then (if
      i.val < 136 then 212 else 213) else (if i.val < 138 then 214 else 210)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 211 else (if i.val < 141 then 156 else
      155)) else (if i.val < 143 then 157 else (if i.val < 144 then 158 else 160))) else (if
      i.val < 148 then (if i.val < 146 then 159 else (if i.val < 147 then 161 else 168)) else
      (if i.val < 150 then (if i.val < 149 then 169 else 166) else (if i.val < 151 then 167 else
      164)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 165 else (if i.val < 154 then 162 else 163)) else (if i.val
      < 156 then 234 else (if i.val < 157 then 233 else 235))) else (if i.val < 161 then (if
      i.val < 159 then 236 else (if i.val < 160 then 238 else 237)) else (if i.val < 162 then
      239 else (if i.val < 163 then 246 else 247)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 244 else (if i.val < 166 then 245 else 242)) else (if i.val <
      168 then 243 else (if i.val < 169 then 240 else 241))) else (if i.val < 173 then (if i.val
      < 171 then 261 else (if i.val < 172 then 260 else 262)) else (if i.val < 175 then (if
      i.val < 174 then 263 else 264) else (if i.val < 176 then 265 else 266))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 267 else (if
      i.val < 179 then 268 else 269)) else (if i.val < 181 then 270 else (if i.val < 182 then
      271 else 122))) else (if i.val < 186 then (if i.val < 184 then 121 else (if i.val < 185
      then 123 else 124)) else (if i.val < 188 then (if i.val < 187 then 125 else 126) else (if
      i.val < 189 then 128 else 127)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 129 else (if i.val < 192 then 138 else 139)) else (if i.val < 194 then 135 else
      (if i.val < 195 then 136 else 137))) else (if i.val < 199 then (if i.val < 197 then 132
      else (if i.val < 198 then 133 else 134)) else (if i.val < 201 then (if i.val < 200 then
      130 else 131) else (if i.val < 202 then 182 else 183)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 184 else (if i.val < 205 then 185 else 186)) else (if
      i.val < 207 then 187 else (if i.val < 208 then 188 else 189))) else (if i.val < 212 then
      (if i.val < 210 then 190 else (if i.val < 211 then 191 else 192)) else (if i.val < 213
      then 193 else (if i.val < 214 then 194 else 195)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 196 else (if i.val < 217 then 197 else 198)) else (if i.val
      < 219 then 199 else (if i.val < 220 then 200 else 222))) else (if i.val < 224 then (if
      i.val < 222 then 220 else (if i.val < 223 then 221 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 228 else 226))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 227 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 140))) else (if i.val < 237 then (if i.val < 235 then 141 else (if i.val <
      236 then 142 else 143)) else (if i.val < 239 then (if i.val < 238 then 144 else 145) else
      (if i.val < 240 then 146 else 147)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 148 else (if i.val < 243 then 149 else 150)) else (if i.val < 245 then
      151 else (if i.val < 246 then 152 else 153))) else (if i.val < 250 then (if i.val < 248
      then 154 else (if i.val < 249 then 172 else 170)) else (if i.val < 252 then (if i.val <
      251 then 171 else 173) else (if i.val < 253 then 174 else 175)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      177 else (if i.val < 256 then 176 else 178)) else (if i.val < 258 then 179 else (if i.val
      < 259 then 180 else 181))) else (if i.val < 263 then (if i.val < 261 then 250 else (if
      i.val < 262 then 249 else 248)) else (if i.val < 264 then 251 else (if i.val < 265 then
      252 else 253)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 255
      else (if i.val < 268 then 254 else 256)) else (if i.val < 270 then 257 else (if i.val <
      271 then 258 else 259))) else (if i.val < 275 then (if i.val < 273 then 275 else (if i.val
      < 274 then 273 else 272)) else (if i.val < 277 then (if i.val < 276 then 274 else 277)
      else (if i.val < 278 then 295 else 300))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 301 else (if i.val < 281 then 303 else 302))
      else (if i.val < 283 then 284 else (if i.val < 284 then 282 else 283))) else (if i.val <
      288 then (if i.val < 286 then 288 else (if i.val < 287 then 290 else 289)) else (if i.val
      < 290 then (if i.val < 289 then 308 else 310) else (if i.val < 291 then 309 else 316))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 315 else (if i.val <
      294 then 317 else 318)) else (if i.val < 296 then 276 else (if i.val < 297 then 279 else
      278))) else (if i.val < 301 then (if i.val < 299 then 281 else (if i.val < 300 then 280
      else 297)) else (if i.val < 303 then (if i.val < 302 then 296 else 298) else (if i.val <
      304 then 299 else 306))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 304 else (if i.val
      < 307 then 305 else 307)) else (if i.val < 309 then 285 else (if i.val < 310 then 286 else
      287))) else (if i.val < 314 then (if i.val < 312 then 293 else (if i.val < 313 then 291
      else 292)) else (if i.val < 315 then 294 else (if i.val < 316 then 313 else 312)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 311 else (if i.val < 319
      then 314 else 322)) else (if i.val < 321 then 320 else (if i.val < 322 then 319 else
      321))) else (if i.val < 326 then (if i.val < 324 then 354 else (if i.val < 325 then 356
      else 355)) else (if i.val < 328 then (if i.val < 327 then 347 else 349) else (if i.val <
      329 then 348 else 343))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 342 else (if i.val < 332 then 341 else 340)) else (if i.val <
      334 then 344 else (if i.val < 335 then 346 else 345))) else (if i.val < 339 then (if i.val
      < 337 then 357 else (if i.val < 338 then 359 else 358)) else (if i.val < 341 then (if
      i.val < 340 then 360 else 350) else (if i.val < 342 then 352 else 351)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 353 else (if i.val < 345 then 373 else
      372)) else (if i.val < 347 then 371 else (if i.val < 348 then 363 else 362))) else (if
      i.val < 352 then (if i.val < 350 then 361 else (if i.val < 351 then 332 else 330)) else
      (if i.val < 354 then (if i.val < 353 then 331 else 329) else (if i.val < 355 then 376 else
      374)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 375 else (if i.val < 358 then 370 else 369)) else (if i.val
      < 360 then 368 else (if i.val < 361 then 367 else 327))) else (if i.val < 365 then (if
      i.val < 363 then 328 else (if i.val < 364 then 326 else 365)) else (if i.val < 366 then
      366 else (if i.val < 367 then 364 else 339)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 337 else (if i.val < 370 then 338 else 336)) else (if i.val <
      372 then 334 else (if i.val < 373 then 335 else 333))) else (if i.val < 377 then (if i.val
      < 375 then 325 else (if i.val < 376 then 324 else 323)) else (if i.val < 379 then (if
      i.val < 378 then 406 else 407) else (if i.val < 380 then 404 else 405))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 388 else (if
      i.val < 383 then 389 else 408)) else (if i.val < 385 then 393 else (if i.val < 386 then
      394 else 391))) else (if i.val < 390 then (if i.val < 388 then 392 else (if i.val < 389
      then 395 else 396)) else (if i.val < 392 then (if i.val < 391 then 397 else 412) else (if
      i.val < 393 then 413 else 410)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 411 else (if i.val < 396 then 381 else 382)) else (if i.val < 398 then 414 else
      (if i.val < 399 then 416 else 379))) else (if i.val < 403 then (if i.val < 401 then 380
      else (if i.val < 402 then 377 else 378)) else (if i.val < 405 then (if i.val < 404 then
      383 else 399) else (if i.val < 406 then 400 else 401))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 402 else (if i.val < 409 then
      403 else 409)) else (if i.val < 411 then 384 else (if i.val < 412 then 385 else 386)))
      else (if i.val < 416 then (if i.val < 414 then 387 else (if i.val < 415 then 390 else
      398)) else (if i.val < 417 then 415 else (if i.val < 418 then 460 else 463)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 464 else (if i.val < 421 then
      461 else 462)) else (if i.val < 423 then 465 else (if i.val < 424 then 466 else 468)))
      else (if i.val < 428 then (if i.val < 426 then 467 else (if i.val < 427 then 469 else
      437)) else (if i.val < 430 then (if i.val < 429 then 440 else 441) else (if i.val < 431
      then 438 else 439))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 442 else (if i.val < 434 then 443 else 445)) else (if i.val < 436
      then 444 else (if i.val < 437 then 446 else 473))) else (if i.val < 441 then (if i.val <
      439 then 476 else (if i.val < 440 then 477 else 474)) else (if i.val < 443 then (if i.val
      < 442 then 475 else 478) else (if i.val < 444 then 479 else 481)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 480 else (if i.val < 447 then 482 else
      486)) else (if i.val < 449 then 487 else (if i.val < 450 then 488 else 417))) else (if
      i.val < 454 then (if i.val < 452 then 420 else (if i.val < 453 then 421 else 418)) else
      (if i.val < 456 then (if i.val < 455 then 419 else 422) else (if i.val < 457 then 423 else
      425)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 424 else (if i.val < 460 then 426 else 450)) else (if i.val
      < 462 then 451 else (if i.val < 463 then 452 else 453))) else (if i.val < 467 then (if
      i.val < 465 then 454 else (if i.val < 466 then 455 else 456)) else (if i.val < 468 then
      457 else (if i.val < 469 then 458 else 459)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 427 else (if i.val < 475 then 428 else 429))) else (if i.val < 479 then (if i.val
      < 477 then 430 else (if i.val < 478 then 431 else 432)) else (if i.val < 481 then (if
      i.val < 480 then 433 else 434) else (if i.val < 482 then 435 else 436))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 447 else (if
      i.val < 485 then 448 else 449)) else (if i.val < 487 then 483 else (if i.val < 488 then
      484 else 485))) else (if i.val < 492 then (if i.val < 490 then 494 else (if i.val < 491
      then 491 else 496)) else (if i.val < 494 then (if i.val < 493 then 498 else 489) else (if
      i.val < 495 then 493 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 490 else (if i.val < 498 then 492 else 497)) else (if i.val < 500 then 519 else
      (if i.val < 501 then 521 else 520))) else (if i.val < 505 then (if i.val < 503 then 522
      else (if i.val < 504 then 506 else 508)) else (if i.val < 507 then (if i.val < 506 then
      507 else 529) else (if i.val < 508 then 531 else 530))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 538 else (if i.val < 511 then 540 else 539)) else (if i.val < 513 then 541 else
      (if i.val < 514 then 542 else 543))) else (if i.val < 518 then (if i.val < 516 then 499
      else (if i.val < 517 then 501 else 500)) else (if i.val < 519 then 502 else (if i.val <
      520 then 515 else 516)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 517 else (if i.val < 523 then 518 else 523)) else (if i.val < 525 then 526 else (if
      i.val < 526 then 524 else 525))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 503)) else (if i.val < 532 then (if i.val < 531 then 504
      else 505) else (if i.val < 533 then 509 else 512))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 510 else (if i.val < 536 then 511
      else 513)) else (if i.val < 538 then 514 else (if i.val < 539 then 532 else 535))) else
      (if i.val < 543 then (if i.val < 541 then 534 else (if i.val < 542 then 533 else 536))
      else (if i.val < 545 then (if i.val < 544 then 537 else 547) else (if i.val < 546 then 545
      else 544)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 546 else
      (if i.val < 549 then 549 else 569)) else (if i.val < 551 then 574 else (if i.val < 552
      then 575 else 577))) else (if i.val < 556 then (if i.val < 554 then 576 else (if i.val <
      555 then 556 else 554)) else (if i.val < 558 then (if i.val < 557 then 555 else 561) else
      (if i.val < 559 then 562 else 564)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 563 else (if i.val < 562 then
      583 else 582)) else (if i.val < 564 then 585 else (if i.val < 565 then 584 else 591)))
      else (if i.val < 569 then (if i.val < 567 then 590 else (if i.val < 568 then 592 else
      593)) else (if i.val < 570 then 548 else (if i.val < 571 then 551 else 550)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 553 else (if i.val < 574 then
      552 else 571)) else (if i.val < 576 then 570 else (if i.val < 577 then 572 else 573)))
      else (if i.val < 581 then (if i.val < 579 then 580 else (if i.val < 580 then 578 else
      579)) else (if i.val < 583 then (if i.val < 582 then 581 else 558) else (if i.val < 584
      then 557 else 559))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 560 else (if i.val < 587 then 567 else 565)) else (if i.val < 589
      then 566 else (if i.val < 590 then 568 else 588))) else (if i.val < 594 then (if i.val <
      592 then 587 else (if i.val < 593 then 586 else 589)) else (if i.val < 596 then (if i.val
      < 595 then 597 else 595) else (if i.val < 597 then 594 else 596)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 601 else (if i.val < 600 then 599 else
      598)) else (if i.val < 602 then 600 else (if i.val < 603 then 606 else 609))) else (if
      i.val < 607 then (if i.val < 605 then 608 else (if i.val < 606 then 607 else 630)) else
      (if i.val < 609 then (if i.val < 608 then 633 else 631) else (if i.val < 610 then 632 else
      638)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 639 else (if
      i.val < 613 then 641 else 640)) else (if i.val < 615 then 614 else (if i.val < 616 then
      617 else 615))) else (if i.val < 620 then (if i.val < 618 then 616 else (if i.val < 619
      then 622 else 623)) else (if i.val < 621 then 625 else (if i.val < 622 then 624 else
      647)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 646 else (if
      i.val < 625 then 649 else 648)) else (if i.val < 627 then 655 else (if i.val < 628 then
      654 else 656))) else (if i.val < 632 then (if i.val < 630 then 657 else (if i.val < 631
      then 602 else 604)) else (if i.val < 634 then (if i.val < 633 then 603 else 605) else (if
      i.val < 635 then 611 else 610))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 613 else (if i.val < 638 then 612 else 635)) else
      (if i.val < 640 then 634 else (if i.val < 641 then 636 else 637))) else (if i.val < 645
      then (if i.val < 643 then 644 else (if i.val < 644 then 642 else 643)) else (if i.val <
      647 then (if i.val < 646 then 645 else 619) else (if i.val < 648 then 618 else 620))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 621 else (if i.val <
      651 then 628 else 626)) else (if i.val < 653 then 627 else (if i.val < 654 then 629 else
      652))) else (if i.val < 658 then (if i.val < 656 then 651 else (if i.val < 657 then 650
      else 653)) else (if i.val < 660 then (if i.val < 659 then 661 else 659) else (if i.val <
      661 then 658 else 660)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 746 else (if i.val < 664 then 745 else
      683)) else (if i.val < 666 then 747 else (if i.val < 667 then 748 else 751))) else (if
      i.val < 671 then (if i.val < 669 then 752 else (if i.val < 670 then 749 else 750)) else
      (if i.val < 672 then 753 else (if i.val < 673 then 754 else 755)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 756 else (if i.val < 676 then 759 else
      760)) else (if i.val < 678 then 757 else (if i.val < 679 then 758 else 761))) else (if
      i.val < 683 then (if i.val < 681 then 762 else (if i.val < 682 then 701 else 700)) else
      (if i.val < 685 then (if i.val < 684 then 702 else 703) else (if i.val < 686 then 704 else
      707))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 708 else (if i.val < 689 then 705 else 706)) else (if i.val < 691 then 709 else
      (if i.val < 692 then 710 else 711))) else (if i.val < 696 then (if i.val < 694 then 712
      else (if i.val < 695 then 715 else 716)) else (if i.val < 698 then (if i.val < 697 then
      713 else 714) else (if i.val < 699 then 717 else 718)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 772 else (if i.val < 702 then 771 else 664)) else
      (if i.val < 704 then 773 else (if i.val < 705 then 774 else 777))) else (if i.val < 709
      then (if i.val < 707 then 778 else (if i.val < 708 then 775 else 776)) else (if i.val <
      711 then (if i.val < 710 then 779 else 780) else (if i.val < 712 then 781 else 782)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 785 else (if i.val < 715 then 786 else 783))
      else (if i.val < 717 then 784 else (if i.val < 718 then 787 else 788))) else (if i.val <
      722 then (if i.val < 720 then 797 else (if i.val < 721 then 798 else 799)) else (if i.val
      < 723 then 800 else (if i.val < 724 then 801 else 802)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 803 else (if i.val < 727 then 804 else 663)) else
      (if i.val < 729 then 662 else (if i.val < 730 then 665 else 666))) else (if i.val < 734
      then (if i.val < 732 then 669 else (if i.val < 733 then 670 else 667)) else (if i.val <
      736 then (if i.val < 735 then 668 else 671) else (if i.val < 737 then 672 else 673)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      674 else (if i.val < 740 then 677 else 678)) else (if i.val < 742 then 675 else (if i.val
      < 743 then 676 else 679))) else (if i.val < 747 then (if i.val < 745 then 680 else (if
      i.val < 746 then 727 else 728)) else (if i.val < 749 then (if i.val < 748 then 729 else
      730) else (if i.val < 750 then 731 else 732)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 733 else (if i.val < 753 then 734 else 735)) else (if i.val <
      755 then 736 else (if i.val < 756 then 737 else 738))) else (if i.val < 760 then (if i.val
      < 758 then 739 else (if i.val < 759 then 740 else 741)) else (if i.val < 762 then (if
      i.val < 761 then 742 else 743) else (if i.val < 763 then 744 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 681 else 682)) else (if i.val < 774 then 684 else (if i.val < 775
      then 685 else 686)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      687 else (if i.val < 778 then 688 else 689)) else (if i.val < 780 then 690 else (if i.val
      < 781 then 691 else 692))) else (if i.val < 785 then (if i.val < 783 then 693 else (if
      i.val < 784 then 694 else 695)) else (if i.val < 787 then (if i.val < 786 then 696 else
      697) else (if i.val < 788 then 698 else 699))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 719 else (if i.val < 791 then 720 else
      721)) else (if i.val < 793 then 722 else (if i.val < 794 then 723 else 724))) else (if
      i.val < 798 then (if i.val < 796 then 725 else (if i.val < 797 then 726 else 789)) else
      (if i.val < 800 then (if i.val < 799 then 790 else 791) else (if i.val < 801 then 792 else
      793)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 794 else (if
      i.val < 804 then 795 else 796)) else (if i.val < 806 then 810 else (if i.val < 807 then
      807 else 812))) else (if i.val < 811 then (if i.val < 809 then 814 else (if i.val < 810
      then 805 else 809)) else (if i.val < 813 then (if i.val < 812 then 811 else 806) else (if
      i.val < 814 then 808 else 813)))))))))))
  invFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 16 else (if i.val < 2 then 18 else 15)) else (if i.val < 4 then 17 else (if i.val <
      5 then 31 else 32))) else (if i.val < 9 then (if i.val < 7 then 33 else (if i.val < 8 then
      6 else 5)) else (if i.val < 10 then 4 else (if i.val < 11 then 35 else 36)))) else (if
      i.val < 18 then (if i.val < 15 then (if i.val < 13 then 34 else (if i.val < 14 then 37
      else 38)) else (if i.val < 16 then 19 else (if i.val < 17 then 20 else 21))) else (if
      i.val < 21 then (if i.val < 19 then 22 else (if i.val < 20 then 2 else 0)) else (if i.val
      < 23 then (if i.val < 22 then 3 else 1) else (if i.val < 24 then 25 else 26))))) else (if
      i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 27 else (if
      i.val < 27 then 28 else 23)) else (if i.val < 29 then 24 else (if i.val < 30 then 29 else
      30))) else (if i.val < 34 then (if i.val < 32 then 9 else (if i.val < 33 then 8 else 7))
      else (if i.val < 35 then 41 else (if i.val < 36 then 40 else 39)))) else (if i.val < 43
      then (if i.val < 40 then (if i.val < 38 then 42 else (if i.val < 39 then 43 else 11)) else
      (if i.val < 41 then 10 else (if i.val < 42 then 12 else 13))) else (if i.val < 46 then (if
      i.val < 44 then 14 else (if i.val < 45 then 46 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 47 else 44) else (if i.val < 49 then 77 else 78)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 75
      else (if i.val < 52 then 76 else 69)) else (if i.val < 54 then 68 else (if i.val < 55 then
      80 else 79))) else (if i.val < 59 then (if i.val < 57 then 81 else (if i.val < 58 then 93
      else 94)) else (if i.val < 60 then 95 else (if i.val < 61 then 96 else 53)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 52 else (if i.val < 64 then 97
      else 59)) else (if i.val < 66 then 60 else (if i.val < 67 then 57 else 58))) else (if
      i.val < 71 then (if i.val < 69 then 61 else (if i.val < 70 then 62 else 63)) else (if
      i.val < 73 then (if i.val < 72 then 99 else 100) else (if i.val < 74 then 98 else 101)))))
      else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then 82
      else (if i.val < 77 then 83 else 84)) else (if i.val < 79 then 85 else (if i.val < 80 then
      86 else 87))) else (if i.val < 84 then (if i.val < 82 then 88 else (if i.val < 83 then 50
      else 51)) else (if i.val < 86 then (if i.val < 85 then 48 else 49) else (if i.val < 87
      then 55 else 54)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then 56
      else (if i.val < 90 then 90 else 91)) else (if i.val < 92 then 89 else (if i.val < 93 then
      92 else 66))) else (if i.val < 97 then (if i.val < 95 then 67 else (if i.val < 96 then 64
      else 65)) else (if i.val < 99 then (if i.val < 98 then 70 else 104) else (if i.val < 100
      then 103 else 102))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113
      then (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 105 else (if i.val <
      103 then 72 else 71)) else (if i.val < 105 then 73 else (if i.val < 106 then 74 else
      116))) else (if i.val < 110 then (if i.val < 108 then 115 else (if i.val < 109 then 114
      else 119)) else (if i.val < 111 then 120 else (if i.val < 112 then 108 else 110)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 109 else (if i.val < 115
      then 111 else 117)) else (if i.val < 117 then 118 else (if i.val < 118 then 107 else
      106))) else (if i.val < 122 then (if i.val < 120 then 113 else (if i.val < 121 then 112
      else 183)) else (if i.val < 124 then (if i.val < 123 then 182 else 184) else (if i.val <
      125 then 185 else 186))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 187 else (if i.val < 128 then 189 else 188)) else (if i.val <
      130 then 190 else (if i.val < 131 then 199 else 200))) else (if i.val < 135 then (if i.val
      < 133 then 196 else (if i.val < 134 then 197 else 198)) else (if i.val < 137 then (if
      i.val < 136 then 193 else 194) else (if i.val < 138 then 195 else 191)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 192 else (if i.val < 141 then 233 else
      234)) else (if i.val < 143 then 235 else (if i.val < 144 then 236 else 237))) else (if
      i.val < 148 then (if i.val < 146 then 238 else (if i.val < 147 then 239 else 240)) else
      (if i.val < 150 then (if i.val < 149 then 241 else 242) else (if i.val < 151 then 243 else
      244)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 245 else (if i.val < 154 then 246 else 247)) else (if i.val
      < 156 then 141 else (if i.val < 157 then 140 else 142))) else (if i.val < 161 then (if
      i.val < 159 then 143 else (if i.val < 160 then 145 else 144)) else (if i.val < 162 then
      146 else (if i.val < 163 then 153 else 154)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 151 else (if i.val < 166 then 152 else 149)) else (if i.val <
      168 then 150 else (if i.val < 169 then 147 else 148))) else (if i.val < 173 then (if i.val
      < 171 then 249 else (if i.val < 172 then 250 else 248)) else (if i.val < 175 then (if
      i.val < 174 then 251 else 252) else (if i.val < 176 then 253 else 255))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 254 else (if
      i.val < 179 then 256 else 257)) else (if i.val < 181 then 258 else (if i.val < 182 then
      259 else 201))) else (if i.val < 186 then (if i.val < 184 then 202 else (if i.val < 185
      then 203 else 204)) else (if i.val < 188 then (if i.val < 187 then 205 else 206) else (if
      i.val < 189 then 207 else 208)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 209 else (if i.val < 192 then 210 else 211)) else (if i.val < 194 then 212 else
      (if i.val < 195 then 213 else 214))) else (if i.val < 199 then (if i.val < 197 then 215
      else (if i.val < 198 then 216 else 217)) else (if i.val < 201 then (if i.val < 200 then
      218 else 219) else (if i.val < 202 then 122 else 121)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 123 else (if i.val < 205 then 124 else 125)) else (if
      i.val < 207 then 126 else (if i.val < 208 then 128 else 127))) else (if i.val < 212 then
      (if i.val < 210 then 129 else (if i.val < 211 then 138 else 139)) else (if i.val < 213
      then 135 else (if i.val < 214 then 136 else 137)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 132 else (if i.val < 217 then 133 else 134)) else (if i.val
      < 219 then 130 else (if i.val < 220 then 131 else 221))) else (if i.val < 224 then (if
      i.val < 222 then 222 else (if i.val < 223 then 220 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 227 else 228))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 226 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 156))) else (if i.val < 237 then (if i.val < 235 then 155 else (if i.val <
      236 then 157 else 158)) else (if i.val < 239 then (if i.val < 238 then 160 else 159) else
      (if i.val < 240 then 161 else 168)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 169 else (if i.val < 243 then 166 else 167)) else (if i.val < 245 then
      164 else (if i.val < 246 then 165 else 162))) else (if i.val < 250 then (if i.val < 248
      then 163 else (if i.val < 249 then 262 else 261)) else (if i.val < 252 then (if i.val <
      251 then 260 else 263) else (if i.val < 253 then 264 else 265)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      267 else (if i.val < 256 then 266 else 268)) else (if i.val < 258 then 269 else (if i.val
      < 259 then 270 else 271))) else (if i.val < 263 then (if i.val < 261 then 171 else (if
      i.val < 262 then 170 else 172)) else (if i.val < 264 then 173 else (if i.val < 265 then
      174 else 175)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 176
      else (if i.val < 268 then 177 else 178)) else (if i.val < 270 then 179 else (if i.val <
      271 then 180 else 181))) else (if i.val < 275 then (if i.val < 273 then 274 else (if i.val
      < 274 then 273 else 275)) else (if i.val < 277 then (if i.val < 276 then 272 else 295)
      else (if i.val < 278 then 276 else 297))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 296 else (if i.val < 281 then 299 else 298))
      else (if i.val < 283 then 283 else (if i.val < 284 then 284 else 282))) else (if i.val <
      288 then (if i.val < 286 then 308 else (if i.val < 287 then 309 else 310)) else (if i.val
      < 290 then (if i.val < 289 then 285 else 287) else (if i.val < 291 then 286 else 312))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 313 else (if i.val <
      294 then 311 else 314)) else (if i.val < 296 then 277 else (if i.val < 297 then 301 else
      300))) else (if i.val < 301 then (if i.val < 299 then 302 else (if i.val < 300 then 303
      else 278)) else (if i.val < 303 then (if i.val < 302 then 279 else 281) else (if i.val <
      304 then 280 else 305))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 306 else (if i.val
      < 307 then 304 else 307)) else (if i.val < 309 then 288 else (if i.val < 310 then 290 else
      289))) else (if i.val < 314 then (if i.val < 312 then 317 else (if i.val < 313 then 316
      else 315)) else (if i.val < 315 then 318 else (if i.val < 316 then 292 else 291)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 293 else (if i.val < 319
      then 294 else 321)) else (if i.val < 321 then 320 else (if i.val < 322 then 322 else
      319))) else (if i.val < 326 then (if i.val < 324 then 376 else (if i.val < 325 then 375
      else 374)) else (if i.val < 328 then (if i.val < 327 then 363 else 361) else (if i.val <
      329 then 362 else 353))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 351 else (if i.val < 332 then 352 else 350)) else (if i.val <
      334 then 373 else (if i.val < 335 then 371 else 372))) else (if i.val < 339 then (if i.val
      < 337 then 370 else (if i.val < 338 then 368 else 369)) else (if i.val < 341 then (if
      i.val < 340 then 367 else 332) else (if i.val < 342 then 331 else 330)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 329 else (if i.val < 345 then 333 else
      335)) else (if i.val < 347 then 334 else (if i.val < 348 then 326 else 328))) else (if
      i.val < 352 then (if i.val < 350 then 327 else (if i.val < 351 then 340 else 342)) else
      (if i.val < 354 then (if i.val < 353 then 341 else 343) else (if i.val < 355 then 323 else
      325)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 324 else (if i.val < 358 then 336 else 338)) else (if i.val
      < 360 then 337 else (if i.val < 361 then 339 else 349))) else (if i.val < 365 then (if
      i.val < 363 then 348 else (if i.val < 364 then 347 else 366)) else (if i.val < 366 then
      364 else (if i.val < 367 then 365 else 360)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 359 else (if i.val < 370 then 358 else 357)) else (if i.val <
      372 then 346 else (if i.val < 373 then 345 else 344))) else (if i.val < 377 then (if i.val
      < 375 then 355 else (if i.val < 376 then 356 else 354)) else (if i.val < 379 then (if
      i.val < 378 then 401 else 402) else (if i.val < 380 then 399 else 400))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 395 else (if
      i.val < 383 then 396 else 403)) else (if i.val < 385 then 410 else (if i.val < 386 then
      411 else 412))) else (if i.val < 390 then (if i.val < 388 then 413 else (if i.val < 389
      then 381 else 382)) else (if i.val < 392 then (if i.val < 391 then 414 else 386) else (if
      i.val < 393 then 387 else 384)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 385 else (if i.val < 396 then 388 else 389)) else (if i.val < 398 then 390 else
      (if i.val < 399 then 415 else 404))) else (if i.val < 403 then (if i.val < 401 then 405
      else (if i.val < 402 then 406 else 407)) else (if i.val < 405 then (if i.val < 404 then
      408 else 379) else (if i.val < 406 then 380 else 377))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 378 else (if i.val < 409 then
      383 else 409)) else (if i.val < 411 then 393 else (if i.val < 412 then 394 else 391)))
      else (if i.val < 416 then (if i.val < 414 then 392 else (if i.val < 415 then 397 else
      416)) else (if i.val < 417 then 398 else (if i.val < 418 then 450 else 453)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 454 else (if i.val < 421 then
      451 else 452)) else (if i.val < 423 then 455 else (if i.val < 424 then 456 else 458)))
      else (if i.val < 428 then (if i.val < 426 then 457 else (if i.val < 427 then 459 else
      473)) else (if i.val < 430 then (if i.val < 429 then 474 else 475) else (if i.val < 431
      then 476 else 477))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 478 else (if i.val < 434 then 479 else 480)) else (if i.val < 436
      then 481 else (if i.val < 437 then 482 else 427))) else (if i.val < 441 then (if i.val <
      439 then 430 else (if i.val < 440 then 431 else 428)) else (if i.val < 443 then (if i.val
      < 442 then 429 else 432) else (if i.val < 444 then 433 else 435)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 434 else (if i.val < 447 then 436 else
      483)) else (if i.val < 449 then 484 else (if i.val < 450 then 485 else 460))) else (if
      i.val < 454 then (if i.val < 452 then 461 else (if i.val < 453 then 462 else 463)) else
      (if i.val < 456 then (if i.val < 455 then 464 else 465) else (if i.val < 457 then 466 else
      467)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 468 else (if i.val < 460 then 469 else 417)) else (if i.val
      < 462 then 420 else (if i.val < 463 then 421 else 418))) else (if i.val < 467 then (if
      i.val < 465 then 419 else (if i.val < 466 then 422 else 423)) else (if i.val < 468 then
      425 else (if i.val < 469 then 424 else 426)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 437 else (if i.val < 475 then 440 else 441))) else (if i.val < 479 then (if i.val
      < 477 then 438 else (if i.val < 478 then 439 else 442)) else (if i.val < 481 then (if
      i.val < 480 then 443 else 445) else (if i.val < 482 then 444 else 446))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 486 else (if
      i.val < 485 then 487 else 488)) else (if i.val < 487 then 447 else (if i.val < 488 then
      448 else 449))) else (if i.val < 492 then (if i.val < 490 then 493 else (if i.val < 491
      then 496 else 490)) else (if i.val < 494 then (if i.val < 493 then 497 else 494) else (if
      i.val < 495 then 489 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 491 else (if i.val < 498 then 498 else 492)) else (if i.val < 500 then 515 else
      (if i.val < 501 then 517 else 516))) else (if i.val < 505 then (if i.val < 503 then 518
      else (if i.val < 504 then 529 else 530)) else (if i.val < 507 then (if i.val < 506 then
      531 else 503) else (if i.val < 508 then 505 else 504))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 532 else (if i.val < 511 then 534 else 535)) else (if i.val < 513 then 533 else
      (if i.val < 514 then 536 else 537))) else (if i.val < 518 then (if i.val < 516 then 519
      else (if i.val < 517 then 520 else 521)) else (if i.val < 519 then 522 else (if i.val <
      520 then 499 else 501)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 500 else (if i.val < 523 then 502 else 523)) else (if i.val < 525 then 525 else (if
      i.val < 526 then 526 else 524))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 506)) else (if i.val < 532 then (if i.val < 531 then 508
      else 507) else (if i.val < 533 then 538 else 541))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 540 else (if i.val < 536 then 539
      else 542)) else (if i.val < 538 then 543 else (if i.val < 539 then 509 else 511))) else
      (if i.val < 543 then (if i.val < 541 then 510 else (if i.val < 542 then 512 else 513))
      else (if i.val < 545 then (if i.val < 544 then 514 else 546) else (if i.val < 546 then 545
      else 547)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 544 else
      (if i.val < 549 then 569 else 548)) else (if i.val < 551 then 571 else (if i.val < 552
      then 570 else 573))) else (if i.val < 556 then (if i.val < 554 then 572 else (if i.val <
      555 then 555 else 556)) else (if i.val < 558 then (if i.val < 557 then 554 else 583) else
      (if i.val < 559 then 582 else 584)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 585 else (if i.val < 562 then
      557 else 558)) else (if i.val < 564 then 560 else (if i.val < 565 then 559 else 587)))
      else (if i.val < 569 then (if i.val < 567 then 588 else (if i.val < 568 then 586 else
      589)) else (if i.val < 570 then 549 else (if i.val < 571 then 575 else 574)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 576 else (if i.val < 574 then
      577 else 550)) else (if i.val < 576 then 551 else (if i.val < 577 then 553 else 552)))
      else (if i.val < 581 then (if i.val < 579 then 579 else (if i.val < 580 then 580 else
      578)) else (if i.val < 583 then (if i.val < 582 then 581 else 562) else (if i.val < 584
      then 561 else 564))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 563 else (if i.val < 587 then 592 else 591)) else (if i.val < 589
      then 590 else (if i.val < 590 then 593 else 566))) else (if i.val < 594 then (if i.val <
      592 then 565 else (if i.val < 593 then 567 else 568)) else (if i.val < 596 then (if i.val
      < 595 then 596 else 595) else (if i.val < 597 then 597 else 594)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 600 else (if i.val < 600 then 599 else
      601)) else (if i.val < 602 then 598 else (if i.val < 603 then 630 else 632))) else (if
      i.val < 607 then (if i.val < 605 then 631 else (if i.val < 606 then 633 else 602)) else
      (if i.val < 609 then (if i.val < 608 then 605 else 604) else (if i.val < 610 then 603 else
      635)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 634 else (if
      i.val < 613 then 637 else 636)) else (if i.val < 615 then 614 else (if i.val < 616 then
      616 else 617))) else (if i.val < 620 then (if i.val < 618 then 615 else (if i.val < 619
      then 647 else 646)) else (if i.val < 621 then 648 else (if i.val < 622 then 649 else
      618)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 619 else (if
      i.val < 625 then 621 else 620)) else (if i.val < 627 then 651 else (if i.val < 628 then
      652 else 650))) else (if i.val < 632 then (if i.val < 630 then 653 else (if i.val < 631
      then 606 else 608)) else (if i.val < 634 then (if i.val < 633 then 609 else 607) else (if
      i.val < 635 then 639 else 638))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 640 else (if i.val < 638 then 641 else 610)) else
      (if i.val < 640 then 611 else (if i.val < 641 then 613 else 612))) else (if i.val < 645
      then (if i.val < 643 then 643 else (if i.val < 644 then 644 else 642)) else (if i.val <
      647 then (if i.val < 646 then 645 else 623) else (if i.val < 648 then 622 else 625))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 624 else (if i.val <
      651 then 656 else 655)) else (if i.val < 653 then 654 else (if i.val < 654 then 657 else
      627))) else (if i.val < 658 then (if i.val < 656 then 626 else (if i.val < 657 then 628
      else 629)) else (if i.val < 660 then (if i.val < 659 then 660 else 659) else (if i.val <
      661 then 661 else 658)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 728 else (if i.val < 664 then 727 else
      702)) else (if i.val < 666 then 729 else (if i.val < 667 then 730 else 733))) else (if
      i.val < 671 then (if i.val < 669 then 734 else (if i.val < 670 then 731 else 732)) else
      (if i.val < 672 then 735 else (if i.val < 673 then 736 else 737)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 738 else (if i.val < 676 then 741 else
      742)) else (if i.val < 678 then 739 else (if i.val < 679 then 740 else 743))) else (if
      i.val < 683 then (if i.val < 681 then 744 else (if i.val < 682 then 771 else 772)) else
      (if i.val < 685 then (if i.val < 684 then 664 else 773) else (if i.val < 686 then 774 else
      775))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 776 else (if i.val < 689 then 777 else 778)) else (if i.val < 691 then 779 else
      (if i.val < 692 then 780 else 781))) else (if i.val < 696 then (if i.val < 694 then 782
      else (if i.val < 695 then 783 else 784)) else (if i.val < 698 then (if i.val < 697 then
      785 else 786) else (if i.val < 699 then 787 else 788)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 682 else (if i.val < 702 then 681 else 683)) else
      (if i.val < 704 then 684 else (if i.val < 705 then 685 else 688))) else (if i.val < 709
      then (if i.val < 707 then 689 else (if i.val < 708 then 686 else 687)) else (if i.val <
      711 then (if i.val < 710 then 690 else 691) else (if i.val < 712 then 692 else 693)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 696 else (if i.val < 715 then 697 else 694))
      else (if i.val < 717 then 695 else (if i.val < 718 then 698 else 699))) else (if i.val <
      722 then (if i.val < 720 then 789 else (if i.val < 721 then 790 else 791)) else (if i.val
      < 723 then 792 else (if i.val < 724 then 793 else 794)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 795 else (if i.val < 727 then 796 else 745)) else
      (if i.val < 729 then 746 else (if i.val < 730 then 747 else 748))) else (if i.val < 734
      then (if i.val < 732 then 749 else (if i.val < 733 then 750 else 751)) else (if i.val <
      736 then (if i.val < 735 then 752 else 753) else (if i.val < 737 then 754 else 755)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      756 else (if i.val < 740 then 757 else 758)) else (if i.val < 742 then 759 else (if i.val
      < 743 then 760 else 761))) else (if i.val < 747 then (if i.val < 745 then 762 else (if
      i.val < 746 then 663 else 662)) else (if i.val < 749 then (if i.val < 748 then 665 else
      666) else (if i.val < 750 then 669 else 670)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 667 else (if i.val < 753 then 668 else 671)) else (if i.val <
      755 then 672 else (if i.val < 756 then 673 else 674))) else (if i.val < 760 then (if i.val
      < 758 then 677 else (if i.val < 759 then 678 else 675)) else (if i.val < 762 then (if
      i.val < 761 then 676 else 679) else (if i.val < 763 then 680 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 701 else 700)) else (if i.val < 774 then 703 else (if i.val < 775
      then 704 else 707)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      708 else (if i.val < 778 then 705 else 706)) else (if i.val < 780 then 709 else (if i.val
      < 781 then 710 else 711))) else (if i.val < 785 then (if i.val < 783 then 712 else (if
      i.val < 784 then 715 else 716)) else (if i.val < 787 then (if i.val < 786 then 713 else
      714) else (if i.val < 788 then 717 else 718))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 797 else (if i.val < 791 then 798 else
      799)) else (if i.val < 793 then 800 else (if i.val < 794 then 801 else 802))) else (if
      i.val < 798 then (if i.val < 796 then 803 else (if i.val < 797 then 804 else 719)) else
      (if i.val < 800 then (if i.val < 799 then 720 else 721) else (if i.val < 801 then 722 else
      723)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 724 else (if
      i.val < 804 then 725 else 726)) else (if i.val < 806 then 809 else (if i.val < 807 then
      812 else 806))) else (if i.val < 811 then (if i.val < 809 then 813 else (if i.val < 810
      then 810 else 805)) else (if i.val < 813 then (if i.val < 812 then 811 else 807) else (if
      i.val < 814 then 814 else 808)))))))))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed vertex, edge and branch bijections for this frame permutation. -/
def hint3 : Fin 815 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
    (if i.val < 25 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 37 then ⟨[0, 1], [0], [false]⟩
    else (if i.val < 43 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 46 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 48 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))))) else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53
    then (if i.val < 51 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 52 then ⟨[0,
    1, 2], [0, 1], [false, false]⟩ else ⟨[1, 0, 2], [1, 0], [false, false]⟩)) else (if i.val <
    54 then ⟨[1, 0, 2], [1, 0], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else
    ⟨[0, 1, 2], [0, 1], [false, false]⟩) else (if i.val < 68 then ⟨[0, 1, 2], [0, 1], [false,
    false]⟩ else (if i.val < 71 then (if i.val < 69 then ⟨[1, 0, 2], [1, 0], [false, false]⟩
    else (if i.val < 70 then ⟨[1, 0, 2], [1, 0], [false, false]⟩ else ⟨[0, 1, 2], [0, 1],
    [false, false]⟩)) else ⟨[0, 1, 2], [0, 1], [false, false]⟩))) else ⟨[0, 1, 2], [0, 1],
    [false, false]⟩)) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if
    i.val < 107 then (if i.val < 104 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val <
    105 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 106 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩))) else (if i.val <
    110 then (if i.val < 108 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if
    i.val < 109 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1,
    2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else
    (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 115 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false,
    false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1,
    2], [false, false, false]⟩) else (if i.val < 122 then (if i.val < 120 then ⟨[0, 1, 2, 3],
    [0, 1, 2], [false, false, false]⟩ else (if i.val < 121 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else ⟨[0, 1, 2], [0, 1],
    [false, false]⟩))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129 then ⟨[0,
    1, 2], [0, 1], [false, false]⟩ else (if i.val < 130 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else ⟨[0, 2, 1], [0, 1], [false, true]⟩)) else ⟨[0, 2, 1], [0, 1], [false, true]⟩) else (if
    i.val < 145 then (if i.val < 142 then (if i.val < 140 then ⟨[0, 2, 1], [0, 1], [false,
    true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)
    else (if i.val < 148 then (if i.val < 146 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if
    i.val < 147 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 2, 1], [0, 1], [false,
    true]⟩)) else ⟨[0, 2, 1], [0, 1], [false, true]⟩)))) else (if i.val < 177 then (if i.val <
    164 then (if i.val < 158 then (if i.val < 155 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else
    ⟨[0, 1, 2], [0, 1], [false, false]⟩) else (if i.val < 161 then ⟨[0, 1, 2], [0, 1], [false,
    false]⟩ else (if i.val < 162 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 2, 1], [0,
    1], [false, true]⟩))) else (if i.val < 170 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else ⟨[0,
    1, 2], [0, 1], [false, false]⟩)) else (if i.val < 190 then ⟨[0, 1, 2], [0, 1], [false,
    false]⟩ else (if i.val < 196 then (if i.val < 193 then (if i.val < 191 then ⟨[0, 1, 2], [0,
    1], [false, false]⟩ else ⟨[0, 2, 1], [0, 1], [false, true]⟩) else ⟨[0, 2, 1], [0, 1],
    [false, true]⟩) else (if i.val < 199 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else (if i.val
    < 201 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))))))) else (if i.val < 305 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val
    < 356 then (if i.val < 330 then (if i.val < 317 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else (if i.val < 323 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 326 then ⟨[0,
    1, 2], [0, 1], [false, false]⟩ else (if i.val < 328 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else (if i.val < 329 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[2, 1, 0], [1, 0],
    [true, true]⟩))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333 then ⟨[2,
    1, 0], [1, 0], [true, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2], [0,
    1], [false, false]⟩) else (if i.val < 349 then (if i.val < 346 then (if i.val < 344 then
    ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩) else ⟨[2, 1, 0],
    [1, 0], [true, true]⟩) else ⟨[2, 1, 0], [1, 0], [true, true]⟩))) else (if i.val < 381 then
    (if i.val < 368 then (if i.val < 362 then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else (if i.val <
    365 then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else (if i.val < 366 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩))) else (if i.val < 374 then ⟨[2, 1,
    0], [1, 0], [true, true]⟩ else (if i.val < 377 then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 394 then (if i.val <
    387 then (if i.val < 384 then (if i.val < 382 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false,
    false]⟩ else (if i.val < 383 then ⟨[1, 0, 3, 2], [1, 0, 2], [false, false, true]⟩ else ⟨[0,
    1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 400 then
    (if i.val < 397 then (if i.val < 395 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩
    else (if i.val < 396 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false, false]⟩ else ⟨[1, 0, 3,
    2], [1, 0, 2], [false, false, true]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)))))) else (if i.val < 611
    then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 425 then ⟨[0, 1, 2, 3],
    [0, 1, 2], [false, false, false]⟩ else (if i.val < 428 then (if i.val < 426 then ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 427 then ⟨[0, 3, 2, 1], [0, 2, 1],
    [false, true, true]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 445 then (if i.val < 438 then (if
    i.val < 435 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 436 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 437 then ⟨[0, 3, 2, 1],
    [0, 2, 1], [false, true, true]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)))
    else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 451 then (if i.val <
    448 then (if i.val < 446 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if
    i.val < 447 then ⟨[0, 3, 2, 1], [0, 2, 1], [false, true, true]⟩ else ⟨[0, 1, 2, 3], [0, 1,
    2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 483 then (if i.val <
    470 then (if i.val < 464 then (if i.val < 461 then (if i.val < 459 then ⟨[0, 1, 2, 3], [0,
    1, 2], [false, false, false]⟩ else (if i.val < 460 then ⟨[0, 3, 2, 1], [0, 2, 1], [false,
    true, true]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0,
    1, 2], [false, false, false]⟩) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 496 then (if i.val < 489
    then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩) else (if i.val < 502 then (if i.val < 499 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else ⟨[0, 1], [0, 1], [false, false]⟩) else ⟨[0, 1], [0, 1], [false, false]⟩)))) else ⟨[0,
    1], [0, 1], [false, false]⟩) else (if i.val < 713 then (if i.val < 662 then ⟨[0, 1], [0, 1],
    [false, false]⟩ else (if i.val < 687 then (if i.val < 674 then (if i.val < 668 then (if
    i.val < 665 then (if i.val < 663 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if
    i.val < 664 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 0, 2], [0, 2, 1],
    [false, false, false]⟩)) else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1,
    2], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩)
    else (if i.val < 700 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 706
    then (if i.val < 703 then (if i.val < 701 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩
    else (if i.val < 702 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 0, 2], [0,
    2, 1], [false, false, false]⟩)) else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩) else
    ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩)))) else (if i.val < 764 then ⟨[0, 1, 2], [0,
    1, 2], [false, false, false]⟩ else (if i.val < 789 then ⟨[0, 1, 2], [0, 1, 2], [false,
    false, false]⟩ else (if i.val < 802 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else
    (if i.val < 808 then (if i.val < 805 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else
    ⟨[0, 1], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1], [0, 1, 2], [false, false,
    false]⟩))))))))

/-- The kernel checks the supplied bijections without repeating permutation search. -/
theorem hints_valid3 : ∀ i, (hint3 i).check ((L24Graphs.graph i).relabel labels3)
    (L24Graphs.graph (destination3 i)) = true := by
  decide +kernel

/-- Every column is transported as a full decorated labelled graph. -/
theorem covered3 : ∀ i, ((L24Graphs.graph i).relabel labels3).isomorphic?
    (L24Graphs.graph (destination3 i)) = true := by
  intro i
  exact (hint3 i).check_sound _ _ (hints_valid3 i)

/-- The 4-th permutation of the three free markings; old labels map covariantly. -/
def labels4 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 3, 0]
  invFun := ![3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A candidate bijection of the held frame columns. -/
def destination4 : Equiv.Perm (Fin 815) where
  toFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 16 else (if i.val < 2 then 18 else 15)) else (if i.val < 4 then 17 else (if i.val <
      5 then 31 else 32))) else (if i.val < 9 then (if i.val < 7 then 33 else (if i.val < 8 then
      6 else 5)) else (if i.val < 10 then 4 else (if i.val < 11 then 35 else 36)))) else (if
      i.val < 18 then (if i.val < 15 then (if i.val < 13 then 34 else (if i.val < 14 then 37
      else 38)) else (if i.val < 16 then 19 else (if i.val < 17 then 20 else 21))) else (if
      i.val < 21 then (if i.val < 19 then 22 else (if i.val < 20 then 2 else 0)) else (if i.val
      < 23 then (if i.val < 22 then 3 else 1) else (if i.val < 24 then 25 else 26))))) else (if
      i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 27 else (if
      i.val < 27 then 28 else 23)) else (if i.val < 29 then 24 else (if i.val < 30 then 29 else
      30))) else (if i.val < 34 then (if i.val < 32 then 9 else (if i.val < 33 then 8 else 7))
      else (if i.val < 35 then 41 else (if i.val < 36 then 40 else 39)))) else (if i.val < 43
      then (if i.val < 40 then (if i.val < 38 then 42 else (if i.val < 39 then 43 else 11)) else
      (if i.val < 41 then 10 else (if i.val < 42 then 12 else 13))) else (if i.val < 46 then (if
      i.val < 44 then 14 else (if i.val < 45 then 46 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 47 else 44) else (if i.val < 49 then 77 else 78)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 75
      else (if i.val < 52 then 76 else 69)) else (if i.val < 54 then 68 else (if i.val < 55 then
      80 else 79))) else (if i.val < 59 then (if i.val < 57 then 81 else (if i.val < 58 then 93
      else 94)) else (if i.val < 60 then 95 else (if i.val < 61 then 96 else 53)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 52 else (if i.val < 64 then 97
      else 59)) else (if i.val < 66 then 60 else (if i.val < 67 then 57 else 58))) else (if
      i.val < 71 then (if i.val < 69 then 61 else (if i.val < 70 then 62 else 63)) else (if
      i.val < 73 then (if i.val < 72 then 99 else 100) else (if i.val < 74 then 98 else 101)))))
      else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then 82
      else (if i.val < 77 then 83 else 84)) else (if i.val < 79 then 85 else (if i.val < 80 then
      86 else 87))) else (if i.val < 84 then (if i.val < 82 then 88 else (if i.val < 83 then 50
      else 51)) else (if i.val < 86 then (if i.val < 85 then 48 else 49) else (if i.val < 87
      then 55 else 54)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then 56
      else (if i.val < 90 then 90 else 91)) else (if i.val < 92 then 89 else (if i.val < 93 then
      92 else 66))) else (if i.val < 97 then (if i.val < 95 then 67 else (if i.val < 96 then 64
      else 65)) else (if i.val < 99 then (if i.val < 98 then 70 else 104) else (if i.val < 100
      then 103 else 102))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113
      then (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 105 else (if i.val <
      103 then 72 else 71)) else (if i.val < 105 then 73 else (if i.val < 106 then 74 else
      116))) else (if i.val < 110 then (if i.val < 108 then 115 else (if i.val < 109 then 114
      else 119)) else (if i.val < 111 then 120 else (if i.val < 112 then 108 else 110)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 109 else (if i.val < 115
      then 111 else 117)) else (if i.val < 117 then 118 else (if i.val < 118 then 107 else
      106))) else (if i.val < 122 then (if i.val < 120 then 113 else (if i.val < 121 then 112
      else 183)) else (if i.val < 124 then (if i.val < 123 then 182 else 184) else (if i.val <
      125 then 185 else 186))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 187 else (if i.val < 128 then 189 else 188)) else (if i.val <
      130 then 190 else (if i.val < 131 then 199 else 200))) else (if i.val < 135 then (if i.val
      < 133 then 196 else (if i.val < 134 then 197 else 198)) else (if i.val < 137 then (if
      i.val < 136 then 193 else 194) else (if i.val < 138 then 195 else 191)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 192 else (if i.val < 141 then 233 else
      234)) else (if i.val < 143 then 235 else (if i.val < 144 then 236 else 237))) else (if
      i.val < 148 then (if i.val < 146 then 238 else (if i.val < 147 then 239 else 240)) else
      (if i.val < 150 then (if i.val < 149 then 241 else 242) else (if i.val < 151 then 243 else
      244)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 245 else (if i.val < 154 then 246 else 247)) else (if i.val
      < 156 then 141 else (if i.val < 157 then 140 else 142))) else (if i.val < 161 then (if
      i.val < 159 then 143 else (if i.val < 160 then 145 else 144)) else (if i.val < 162 then
      146 else (if i.val < 163 then 153 else 154)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 151 else (if i.val < 166 then 152 else 149)) else (if i.val <
      168 then 150 else (if i.val < 169 then 147 else 148))) else (if i.val < 173 then (if i.val
      < 171 then 249 else (if i.val < 172 then 250 else 248)) else (if i.val < 175 then (if
      i.val < 174 then 251 else 252) else (if i.val < 176 then 253 else 255))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 254 else (if
      i.val < 179 then 256 else 257)) else (if i.val < 181 then 258 else (if i.val < 182 then
      259 else 201))) else (if i.val < 186 then (if i.val < 184 then 202 else (if i.val < 185
      then 203 else 204)) else (if i.val < 188 then (if i.val < 187 then 205 else 206) else (if
      i.val < 189 then 207 else 208)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 209 else (if i.val < 192 then 210 else 211)) else (if i.val < 194 then 212 else
      (if i.val < 195 then 213 else 214))) else (if i.val < 199 then (if i.val < 197 then 215
      else (if i.val < 198 then 216 else 217)) else (if i.val < 201 then (if i.val < 200 then
      218 else 219) else (if i.val < 202 then 122 else 121)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 123 else (if i.val < 205 then 124 else 125)) else (if
      i.val < 207 then 126 else (if i.val < 208 then 128 else 127))) else (if i.val < 212 then
      (if i.val < 210 then 129 else (if i.val < 211 then 138 else 139)) else (if i.val < 213
      then 135 else (if i.val < 214 then 136 else 137)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 132 else (if i.val < 217 then 133 else 134)) else (if i.val
      < 219 then 130 else (if i.val < 220 then 131 else 221))) else (if i.val < 224 then (if
      i.val < 222 then 222 else (if i.val < 223 then 220 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 227 else 228))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 226 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 156))) else (if i.val < 237 then (if i.val < 235 then 155 else (if i.val <
      236 then 157 else 158)) else (if i.val < 239 then (if i.val < 238 then 160 else 159) else
      (if i.val < 240 then 161 else 168)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 169 else (if i.val < 243 then 166 else 167)) else (if i.val < 245 then
      164 else (if i.val < 246 then 165 else 162))) else (if i.val < 250 then (if i.val < 248
      then 163 else (if i.val < 249 then 262 else 261)) else (if i.val < 252 then (if i.val <
      251 then 260 else 263) else (if i.val < 253 then 264 else 265)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      267 else (if i.val < 256 then 266 else 268)) else (if i.val < 258 then 269 else (if i.val
      < 259 then 270 else 271))) else (if i.val < 263 then (if i.val < 261 then 171 else (if
      i.val < 262 then 170 else 172)) else (if i.val < 264 then 173 else (if i.val < 265 then
      174 else 175)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 176
      else (if i.val < 268 then 177 else 178)) else (if i.val < 270 then 179 else (if i.val <
      271 then 180 else 181))) else (if i.val < 275 then (if i.val < 273 then 274 else (if i.val
      < 274 then 273 else 275)) else (if i.val < 277 then (if i.val < 276 then 272 else 295)
      else (if i.val < 278 then 276 else 297))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 296 else (if i.val < 281 then 299 else 298))
      else (if i.val < 283 then 283 else (if i.val < 284 then 284 else 282))) else (if i.val <
      288 then (if i.val < 286 then 308 else (if i.val < 287 then 309 else 310)) else (if i.val
      < 290 then (if i.val < 289 then 285 else 287) else (if i.val < 291 then 286 else 312))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 313 else (if i.val <
      294 then 311 else 314)) else (if i.val < 296 then 277 else (if i.val < 297 then 301 else
      300))) else (if i.val < 301 then (if i.val < 299 then 302 else (if i.val < 300 then 303
      else 278)) else (if i.val < 303 then (if i.val < 302 then 279 else 281) else (if i.val <
      304 then 280 else 305))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 306 else (if i.val
      < 307 then 304 else 307)) else (if i.val < 309 then 288 else (if i.val < 310 then 290 else
      289))) else (if i.val < 314 then (if i.val < 312 then 317 else (if i.val < 313 then 316
      else 315)) else (if i.val < 315 then 318 else (if i.val < 316 then 292 else 291)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 293 else (if i.val < 319
      then 294 else 321)) else (if i.val < 321 then 320 else (if i.val < 322 then 322 else
      319))) else (if i.val < 326 then (if i.val < 324 then 376 else (if i.val < 325 then 375
      else 374)) else (if i.val < 328 then (if i.val < 327 then 363 else 361) else (if i.val <
      329 then 362 else 353))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 351 else (if i.val < 332 then 352 else 350)) else (if i.val <
      334 then 373 else (if i.val < 335 then 371 else 372))) else (if i.val < 339 then (if i.val
      < 337 then 370 else (if i.val < 338 then 368 else 369)) else (if i.val < 341 then (if
      i.val < 340 then 367 else 332) else (if i.val < 342 then 331 else 330)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 329 else (if i.val < 345 then 333 else
      335)) else (if i.val < 347 then 334 else (if i.val < 348 then 326 else 328))) else (if
      i.val < 352 then (if i.val < 350 then 327 else (if i.val < 351 then 340 else 342)) else
      (if i.val < 354 then (if i.val < 353 then 341 else 343) else (if i.val < 355 then 323 else
      325)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 324 else (if i.val < 358 then 336 else 338)) else (if i.val
      < 360 then 337 else (if i.val < 361 then 339 else 349))) else (if i.val < 365 then (if
      i.val < 363 then 348 else (if i.val < 364 then 347 else 366)) else (if i.val < 366 then
      364 else (if i.val < 367 then 365 else 360)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 359 else (if i.val < 370 then 358 else 357)) else (if i.val <
      372 then 346 else (if i.val < 373 then 345 else 344))) else (if i.val < 377 then (if i.val
      < 375 then 355 else (if i.val < 376 then 356 else 354)) else (if i.val < 379 then (if
      i.val < 378 then 401 else 402) else (if i.val < 380 then 399 else 400))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 395 else (if
      i.val < 383 then 396 else 403)) else (if i.val < 385 then 410 else (if i.val < 386 then
      411 else 412))) else (if i.val < 390 then (if i.val < 388 then 413 else (if i.val < 389
      then 381 else 382)) else (if i.val < 392 then (if i.val < 391 then 414 else 386) else (if
      i.val < 393 then 387 else 384)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 385 else (if i.val < 396 then 388 else 389)) else (if i.val < 398 then 390 else
      (if i.val < 399 then 415 else 404))) else (if i.val < 403 then (if i.val < 401 then 405
      else (if i.val < 402 then 406 else 407)) else (if i.val < 405 then (if i.val < 404 then
      408 else 379) else (if i.val < 406 then 380 else 377))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 378 else (if i.val < 409 then
      383 else 409)) else (if i.val < 411 then 393 else (if i.val < 412 then 394 else 391)))
      else (if i.val < 416 then (if i.val < 414 then 392 else (if i.val < 415 then 397 else
      416)) else (if i.val < 417 then 398 else (if i.val < 418 then 450 else 453)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 454 else (if i.val < 421 then
      451 else 452)) else (if i.val < 423 then 455 else (if i.val < 424 then 456 else 458)))
      else (if i.val < 428 then (if i.val < 426 then 457 else (if i.val < 427 then 459 else
      473)) else (if i.val < 430 then (if i.val < 429 then 474 else 475) else (if i.val < 431
      then 476 else 477))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 478 else (if i.val < 434 then 479 else 480)) else (if i.val < 436
      then 481 else (if i.val < 437 then 482 else 427))) else (if i.val < 441 then (if i.val <
      439 then 430 else (if i.val < 440 then 431 else 428)) else (if i.val < 443 then (if i.val
      < 442 then 429 else 432) else (if i.val < 444 then 433 else 435)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 434 else (if i.val < 447 then 436 else
      483)) else (if i.val < 449 then 484 else (if i.val < 450 then 485 else 460))) else (if
      i.val < 454 then (if i.val < 452 then 461 else (if i.val < 453 then 462 else 463)) else
      (if i.val < 456 then (if i.val < 455 then 464 else 465) else (if i.val < 457 then 466 else
      467)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 468 else (if i.val < 460 then 469 else 417)) else (if i.val
      < 462 then 420 else (if i.val < 463 then 421 else 418))) else (if i.val < 467 then (if
      i.val < 465 then 419 else (if i.val < 466 then 422 else 423)) else (if i.val < 468 then
      425 else (if i.val < 469 then 424 else 426)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 437 else (if i.val < 475 then 440 else 441))) else (if i.val < 479 then (if i.val
      < 477 then 438 else (if i.val < 478 then 439 else 442)) else (if i.val < 481 then (if
      i.val < 480 then 443 else 445) else (if i.val < 482 then 444 else 446))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 486 else (if
      i.val < 485 then 487 else 488)) else (if i.val < 487 then 447 else (if i.val < 488 then
      448 else 449))) else (if i.val < 492 then (if i.val < 490 then 493 else (if i.val < 491
      then 496 else 490)) else (if i.val < 494 then (if i.val < 493 then 497 else 494) else (if
      i.val < 495 then 489 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 491 else (if i.val < 498 then 498 else 492)) else (if i.val < 500 then 515 else
      (if i.val < 501 then 517 else 516))) else (if i.val < 505 then (if i.val < 503 then 518
      else (if i.val < 504 then 529 else 530)) else (if i.val < 507 then (if i.val < 506 then
      531 else 503) else (if i.val < 508 then 505 else 504))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 532 else (if i.val < 511 then 534 else 535)) else (if i.val < 513 then 533 else
      (if i.val < 514 then 536 else 537))) else (if i.val < 518 then (if i.val < 516 then 519
      else (if i.val < 517 then 520 else 521)) else (if i.val < 519 then 522 else (if i.val <
      520 then 499 else 501)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 500 else (if i.val < 523 then 502 else 523)) else (if i.val < 525 then 525 else (if
      i.val < 526 then 526 else 524))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 506)) else (if i.val < 532 then (if i.val < 531 then 508
      else 507) else (if i.val < 533 then 538 else 541))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 540 else (if i.val < 536 then 539
      else 542)) else (if i.val < 538 then 543 else (if i.val < 539 then 509 else 511))) else
      (if i.val < 543 then (if i.val < 541 then 510 else (if i.val < 542 then 512 else 513))
      else (if i.val < 545 then (if i.val < 544 then 514 else 546) else (if i.val < 546 then 545
      else 547)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 544 else
      (if i.val < 549 then 569 else 548)) else (if i.val < 551 then 571 else (if i.val < 552
      then 570 else 573))) else (if i.val < 556 then (if i.val < 554 then 572 else (if i.val <
      555 then 555 else 556)) else (if i.val < 558 then (if i.val < 557 then 554 else 583) else
      (if i.val < 559 then 582 else 584)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 585 else (if i.val < 562 then
      557 else 558)) else (if i.val < 564 then 560 else (if i.val < 565 then 559 else 587)))
      else (if i.val < 569 then (if i.val < 567 then 588 else (if i.val < 568 then 586 else
      589)) else (if i.val < 570 then 549 else (if i.val < 571 then 575 else 574)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 576 else (if i.val < 574 then
      577 else 550)) else (if i.val < 576 then 551 else (if i.val < 577 then 553 else 552)))
      else (if i.val < 581 then (if i.val < 579 then 579 else (if i.val < 580 then 580 else
      578)) else (if i.val < 583 then (if i.val < 582 then 581 else 562) else (if i.val < 584
      then 561 else 564))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 563 else (if i.val < 587 then 592 else 591)) else (if i.val < 589
      then 590 else (if i.val < 590 then 593 else 566))) else (if i.val < 594 then (if i.val <
      592 then 565 else (if i.val < 593 then 567 else 568)) else (if i.val < 596 then (if i.val
      < 595 then 596 else 595) else (if i.val < 597 then 597 else 594)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 600 else (if i.val < 600 then 599 else
      601)) else (if i.val < 602 then 598 else (if i.val < 603 then 630 else 632))) else (if
      i.val < 607 then (if i.val < 605 then 631 else (if i.val < 606 then 633 else 602)) else
      (if i.val < 609 then (if i.val < 608 then 605 else 604) else (if i.val < 610 then 603 else
      635)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 634 else (if
      i.val < 613 then 637 else 636)) else (if i.val < 615 then 614 else (if i.val < 616 then
      616 else 617))) else (if i.val < 620 then (if i.val < 618 then 615 else (if i.val < 619
      then 647 else 646)) else (if i.val < 621 then 648 else (if i.val < 622 then 649 else
      618)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 619 else (if
      i.val < 625 then 621 else 620)) else (if i.val < 627 then 651 else (if i.val < 628 then
      652 else 650))) else (if i.val < 632 then (if i.val < 630 then 653 else (if i.val < 631
      then 606 else 608)) else (if i.val < 634 then (if i.val < 633 then 609 else 607) else (if
      i.val < 635 then 639 else 638))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 640 else (if i.val < 638 then 641 else 610)) else
      (if i.val < 640 then 611 else (if i.val < 641 then 613 else 612))) else (if i.val < 645
      then (if i.val < 643 then 643 else (if i.val < 644 then 644 else 642)) else (if i.val <
      647 then (if i.val < 646 then 645 else 623) else (if i.val < 648 then 622 else 625))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 624 else (if i.val <
      651 then 656 else 655)) else (if i.val < 653 then 654 else (if i.val < 654 then 657 else
      627))) else (if i.val < 658 then (if i.val < 656 then 626 else (if i.val < 657 then 628
      else 629)) else (if i.val < 660 then (if i.val < 659 then 660 else 659) else (if i.val <
      661 then 661 else 658)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 728 else (if i.val < 664 then 727 else
      702)) else (if i.val < 666 then 729 else (if i.val < 667 then 730 else 733))) else (if
      i.val < 671 then (if i.val < 669 then 734 else (if i.val < 670 then 731 else 732)) else
      (if i.val < 672 then 735 else (if i.val < 673 then 736 else 737)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 738 else (if i.val < 676 then 741 else
      742)) else (if i.val < 678 then 739 else (if i.val < 679 then 740 else 743))) else (if
      i.val < 683 then (if i.val < 681 then 744 else (if i.val < 682 then 771 else 772)) else
      (if i.val < 685 then (if i.val < 684 then 664 else 773) else (if i.val < 686 then 774 else
      775))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 776 else (if i.val < 689 then 777 else 778)) else (if i.val < 691 then 779 else
      (if i.val < 692 then 780 else 781))) else (if i.val < 696 then (if i.val < 694 then 782
      else (if i.val < 695 then 783 else 784)) else (if i.val < 698 then (if i.val < 697 then
      785 else 786) else (if i.val < 699 then 787 else 788)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 682 else (if i.val < 702 then 681 else 683)) else
      (if i.val < 704 then 684 else (if i.val < 705 then 685 else 688))) else (if i.val < 709
      then (if i.val < 707 then 689 else (if i.val < 708 then 686 else 687)) else (if i.val <
      711 then (if i.val < 710 then 690 else 691) else (if i.val < 712 then 692 else 693)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 696 else (if i.val < 715 then 697 else 694))
      else (if i.val < 717 then 695 else (if i.val < 718 then 698 else 699))) else (if i.val <
      722 then (if i.val < 720 then 789 else (if i.val < 721 then 790 else 791)) else (if i.val
      < 723 then 792 else (if i.val < 724 then 793 else 794)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 795 else (if i.val < 727 then 796 else 745)) else
      (if i.val < 729 then 746 else (if i.val < 730 then 747 else 748))) else (if i.val < 734
      then (if i.val < 732 then 749 else (if i.val < 733 then 750 else 751)) else (if i.val <
      736 then (if i.val < 735 then 752 else 753) else (if i.val < 737 then 754 else 755)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      756 else (if i.val < 740 then 757 else 758)) else (if i.val < 742 then 759 else (if i.val
      < 743 then 760 else 761))) else (if i.val < 747 then (if i.val < 745 then 762 else (if
      i.val < 746 then 663 else 662)) else (if i.val < 749 then (if i.val < 748 then 665 else
      666) else (if i.val < 750 then 669 else 670)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 667 else (if i.val < 753 then 668 else 671)) else (if i.val <
      755 then 672 else (if i.val < 756 then 673 else 674))) else (if i.val < 760 then (if i.val
      < 758 then 677 else (if i.val < 759 then 678 else 675)) else (if i.val < 762 then (if
      i.val < 761 then 676 else 679) else (if i.val < 763 then 680 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 701 else 700)) else (if i.val < 774 then 703 else (if i.val < 775
      then 704 else 707)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      708 else (if i.val < 778 then 705 else 706)) else (if i.val < 780 then 709 else (if i.val
      < 781 then 710 else 711))) else (if i.val < 785 then (if i.val < 783 then 712 else (if
      i.val < 784 then 715 else 716)) else (if i.val < 787 then (if i.val < 786 then 713 else
      714) else (if i.val < 788 then 717 else 718))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 797 else (if i.val < 791 then 798 else
      799)) else (if i.val < 793 then 800 else (if i.val < 794 then 801 else 802))) else (if
      i.val < 798 then (if i.val < 796 then 803 else (if i.val < 797 then 804 else 719)) else
      (if i.val < 800 then (if i.val < 799 then 720 else 721) else (if i.val < 801 then 722 else
      723)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 724 else (if
      i.val < 804 then 725 else 726)) else (if i.val < 806 then 809 else (if i.val < 807 then
      812 else 806))) else (if i.val < 811 then (if i.val < 809 then 813 else (if i.val < 810
      then 810 else 805)) else (if i.val < 813 then (if i.val < 812 then 811 else 807) else (if
      i.val < 814 then 814 else 808)))))))))))
  invFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 20 else (if i.val < 2 then 22 else 19)) else (if i.val < 4 then 21 else (if i.val <
      5 then 9 else 8))) else (if i.val < 9 then (if i.val < 7 then 7 else (if i.val < 8 then 33
      else 32)) else (if i.val < 10 then 31 else (if i.val < 11 then 40 else 39)))) else (if
      i.val < 18 then (if i.val < 15 then (if i.val < 13 then 41 else (if i.val < 14 then 42
      else 43)) else (if i.val < 16 then 2 else (if i.val < 17 then 0 else 3))) else (if i.val <
      21 then (if i.val < 19 then 1 else (if i.val < 20 then 15 else 16)) else (if i.val < 23
      then (if i.val < 22 then 17 else 18) else (if i.val < 24 then 27 else 28))))) else (if
      i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 23 else (if
      i.val < 27 then 24 else 25)) else (if i.val < 29 then 26 else (if i.val < 30 then 29 else
      30))) else (if i.val < 34 then (if i.val < 32 then 4 else (if i.val < 33 then 5 else 6))
      else (if i.val < 35 then 12 else (if i.val < 36 then 10 else 11)))) else (if i.val < 43
      then (if i.val < 40 then (if i.val < 38 then 13 else (if i.val < 39 then 14 else 36)) else
      (if i.val < 41 then 35 else (if i.val < 42 then 34 else 37))) else (if i.val < 46 then (if
      i.val < 44 then 38 else (if i.val < 45 then 47 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 44 else 46) else (if i.val < 49 then 84 else 85)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 82
      else (if i.val < 52 then 83 else 62)) else (if i.val < 54 then 61 else (if i.val < 55 then
      87 else 86))) else (if i.val < 59 then (if i.val < 57 then 88 else (if i.val < 58 then 66
      else 67)) else (if i.val < 60 then 64 else (if i.val < 61 then 65 else 68)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 69 else (if i.val < 64 then 70
      else 95)) else (if i.val < 66 then 96 else (if i.val < 67 then 93 else 94))) else (if
      i.val < 71 then (if i.val < 69 then 53 else (if i.val < 70 then 52 else 97)) else (if
      i.val < 73 then (if i.val < 72 then 103 else 102) else (if i.val < 74 then 104 else
      105))))) else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76
      then 50 else (if i.val < 77 then 51 else 48)) else (if i.val < 79 then 49 else (if i.val <
      80 then 55 else 54))) else (if i.val < 84 then (if i.val < 82 then 56 else (if i.val < 83
      then 75 else 76)) else (if i.val < 86 then (if i.val < 85 then 77 else 78) else (if i.val
      < 87 then 79 else 80)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then
      81 else (if i.val < 90 then 91 else 89)) else (if i.val < 92 then 90 else (if i.val < 93
      then 92 else 57))) else (if i.val < 97 then (if i.val < 95 then 58 else (if i.val < 96
      then 59 else 60)) else (if i.val < 99 then (if i.val < 98 then 63 else 73) else (if i.val
      < 100 then 71 else 72))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val <
      113 then (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 74 else (if i.val
      < 103 then 100 else 99)) else (if i.val < 105 then 98 else (if i.val < 106 then 101 else
      118))) else (if i.val < 110 then (if i.val < 108 then 117 else (if i.val < 109 then 111
      else 113)) else (if i.val < 111 then 112 else (if i.val < 112 then 114 else 120)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 119 else (if i.val < 115
      then 108 else 107)) else (if i.val < 117 then 106 else (if i.val < 118 then 115 else
      116))) else (if i.val < 122 then (if i.val < 120 then 109 else (if i.val < 121 then 110
      else 202)) else (if i.val < 124 then (if i.val < 123 then 201 else 203) else (if i.val <
      125 then 204 else 205))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 206 else (if i.val < 128 then 208 else 207)) else (if i.val <
      130 then 209 else (if i.val < 131 then 218 else 219))) else (if i.val < 135 then (if i.val
      < 133 then 215 else (if i.val < 134 then 216 else 217)) else (if i.val < 137 then (if
      i.val < 136 then 212 else 213) else (if i.val < 138 then 214 else 210)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 211 else (if i.val < 141 then 156 else
      155)) else (if i.val < 143 then 157 else (if i.val < 144 then 158 else 160))) else (if
      i.val < 148 then (if i.val < 146 then 159 else (if i.val < 147 then 161 else 168)) else
      (if i.val < 150 then (if i.val < 149 then 169 else 166) else (if i.val < 151 then 167 else
      164)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 165 else (if i.val < 154 then 162 else 163)) else (if i.val
      < 156 then 234 else (if i.val < 157 then 233 else 235))) else (if i.val < 161 then (if
      i.val < 159 then 236 else (if i.val < 160 then 238 else 237)) else (if i.val < 162 then
      239 else (if i.val < 163 then 246 else 247)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 244 else (if i.val < 166 then 245 else 242)) else (if i.val <
      168 then 243 else (if i.val < 169 then 240 else 241))) else (if i.val < 173 then (if i.val
      < 171 then 261 else (if i.val < 172 then 260 else 262)) else (if i.val < 175 then (if
      i.val < 174 then 263 else 264) else (if i.val < 176 then 265 else 266))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 267 else (if
      i.val < 179 then 268 else 269)) else (if i.val < 181 then 270 else (if i.val < 182 then
      271 else 122))) else (if i.val < 186 then (if i.val < 184 then 121 else (if i.val < 185
      then 123 else 124)) else (if i.val < 188 then (if i.val < 187 then 125 else 126) else (if
      i.val < 189 then 128 else 127)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 129 else (if i.val < 192 then 138 else 139)) else (if i.val < 194 then 135 else
      (if i.val < 195 then 136 else 137))) else (if i.val < 199 then (if i.val < 197 then 132
      else (if i.val < 198 then 133 else 134)) else (if i.val < 201 then (if i.val < 200 then
      130 else 131) else (if i.val < 202 then 182 else 183)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 184 else (if i.val < 205 then 185 else 186)) else (if
      i.val < 207 then 187 else (if i.val < 208 then 188 else 189))) else (if i.val < 212 then
      (if i.val < 210 then 190 else (if i.val < 211 then 191 else 192)) else (if i.val < 213
      then 193 else (if i.val < 214 then 194 else 195)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 196 else (if i.val < 217 then 197 else 198)) else (if i.val
      < 219 then 199 else (if i.val < 220 then 200 else 222))) else (if i.val < 224 then (if
      i.val < 222 then 220 else (if i.val < 223 then 221 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 228 else 226))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 227 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 140))) else (if i.val < 237 then (if i.val < 235 then 141 else (if i.val <
      236 then 142 else 143)) else (if i.val < 239 then (if i.val < 238 then 144 else 145) else
      (if i.val < 240 then 146 else 147)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 148 else (if i.val < 243 then 149 else 150)) else (if i.val < 245 then
      151 else (if i.val < 246 then 152 else 153))) else (if i.val < 250 then (if i.val < 248
      then 154 else (if i.val < 249 then 172 else 170)) else (if i.val < 252 then (if i.val <
      251 then 171 else 173) else (if i.val < 253 then 174 else 175)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      177 else (if i.val < 256 then 176 else 178)) else (if i.val < 258 then 179 else (if i.val
      < 259 then 180 else 181))) else (if i.val < 263 then (if i.val < 261 then 250 else (if
      i.val < 262 then 249 else 248)) else (if i.val < 264 then 251 else (if i.val < 265 then
      252 else 253)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 255
      else (if i.val < 268 then 254 else 256)) else (if i.val < 270 then 257 else (if i.val <
      271 then 258 else 259))) else (if i.val < 275 then (if i.val < 273 then 275 else (if i.val
      < 274 then 273 else 272)) else (if i.val < 277 then (if i.val < 276 then 274 else 277)
      else (if i.val < 278 then 295 else 300))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 301 else (if i.val < 281 then 303 else 302))
      else (if i.val < 283 then 284 else (if i.val < 284 then 282 else 283))) else (if i.val <
      288 then (if i.val < 286 then 288 else (if i.val < 287 then 290 else 289)) else (if i.val
      < 290 then (if i.val < 289 then 308 else 310) else (if i.val < 291 then 309 else 316))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 315 else (if i.val <
      294 then 317 else 318)) else (if i.val < 296 then 276 else (if i.val < 297 then 279 else
      278))) else (if i.val < 301 then (if i.val < 299 then 281 else (if i.val < 300 then 280
      else 297)) else (if i.val < 303 then (if i.val < 302 then 296 else 298) else (if i.val <
      304 then 299 else 306))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 304 else (if i.val
      < 307 then 305 else 307)) else (if i.val < 309 then 285 else (if i.val < 310 then 286 else
      287))) else (if i.val < 314 then (if i.val < 312 then 293 else (if i.val < 313 then 291
      else 292)) else (if i.val < 315 then 294 else (if i.val < 316 then 313 else 312)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 311 else (if i.val < 319
      then 314 else 322)) else (if i.val < 321 then 320 else (if i.val < 322 then 319 else
      321))) else (if i.val < 326 then (if i.val < 324 then 354 else (if i.val < 325 then 356
      else 355)) else (if i.val < 328 then (if i.val < 327 then 347 else 349) else (if i.val <
      329 then 348 else 343))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 342 else (if i.val < 332 then 341 else 340)) else (if i.val <
      334 then 344 else (if i.val < 335 then 346 else 345))) else (if i.val < 339 then (if i.val
      < 337 then 357 else (if i.val < 338 then 359 else 358)) else (if i.val < 341 then (if
      i.val < 340 then 360 else 350) else (if i.val < 342 then 352 else 351)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 353 else (if i.val < 345 then 373 else
      372)) else (if i.val < 347 then 371 else (if i.val < 348 then 363 else 362))) else (if
      i.val < 352 then (if i.val < 350 then 361 else (if i.val < 351 then 332 else 330)) else
      (if i.val < 354 then (if i.val < 353 then 331 else 329) else (if i.val < 355 then 376 else
      374)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 375 else (if i.val < 358 then 370 else 369)) else (if i.val
      < 360 then 368 else (if i.val < 361 then 367 else 327))) else (if i.val < 365 then (if
      i.val < 363 then 328 else (if i.val < 364 then 326 else 365)) else (if i.val < 366 then
      366 else (if i.val < 367 then 364 else 339)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 337 else (if i.val < 370 then 338 else 336)) else (if i.val <
      372 then 334 else (if i.val < 373 then 335 else 333))) else (if i.val < 377 then (if i.val
      < 375 then 325 else (if i.val < 376 then 324 else 323)) else (if i.val < 379 then (if
      i.val < 378 then 406 else 407) else (if i.val < 380 then 404 else 405))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 388 else (if
      i.val < 383 then 389 else 408)) else (if i.val < 385 then 393 else (if i.val < 386 then
      394 else 391))) else (if i.val < 390 then (if i.val < 388 then 392 else (if i.val < 389
      then 395 else 396)) else (if i.val < 392 then (if i.val < 391 then 397 else 412) else (if
      i.val < 393 then 413 else 410)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 411 else (if i.val < 396 then 381 else 382)) else (if i.val < 398 then 414 else
      (if i.val < 399 then 416 else 379))) else (if i.val < 403 then (if i.val < 401 then 380
      else (if i.val < 402 then 377 else 378)) else (if i.val < 405 then (if i.val < 404 then
      383 else 399) else (if i.val < 406 then 400 else 401))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 402 else (if i.val < 409 then
      403 else 409)) else (if i.val < 411 then 384 else (if i.val < 412 then 385 else 386)))
      else (if i.val < 416 then (if i.val < 414 then 387 else (if i.val < 415 then 390 else
      398)) else (if i.val < 417 then 415 else (if i.val < 418 then 460 else 463)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 464 else (if i.val < 421 then
      461 else 462)) else (if i.val < 423 then 465 else (if i.val < 424 then 466 else 468)))
      else (if i.val < 428 then (if i.val < 426 then 467 else (if i.val < 427 then 469 else
      437)) else (if i.val < 430 then (if i.val < 429 then 440 else 441) else (if i.val < 431
      then 438 else 439))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 442 else (if i.val < 434 then 443 else 445)) else (if i.val < 436
      then 444 else (if i.val < 437 then 446 else 473))) else (if i.val < 441 then (if i.val <
      439 then 476 else (if i.val < 440 then 477 else 474)) else (if i.val < 443 then (if i.val
      < 442 then 475 else 478) else (if i.val < 444 then 479 else 481)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 480 else (if i.val < 447 then 482 else
      486)) else (if i.val < 449 then 487 else (if i.val < 450 then 488 else 417))) else (if
      i.val < 454 then (if i.val < 452 then 420 else (if i.val < 453 then 421 else 418)) else
      (if i.val < 456 then (if i.val < 455 then 419 else 422) else (if i.val < 457 then 423 else
      425)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 424 else (if i.val < 460 then 426 else 450)) else (if i.val
      < 462 then 451 else (if i.val < 463 then 452 else 453))) else (if i.val < 467 then (if
      i.val < 465 then 454 else (if i.val < 466 then 455 else 456)) else (if i.val < 468 then
      457 else (if i.val < 469 then 458 else 459)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 427 else (if i.val < 475 then 428 else 429))) else (if i.val < 479 then (if i.val
      < 477 then 430 else (if i.val < 478 then 431 else 432)) else (if i.val < 481 then (if
      i.val < 480 then 433 else 434) else (if i.val < 482 then 435 else 436))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 447 else (if
      i.val < 485 then 448 else 449)) else (if i.val < 487 then 483 else (if i.val < 488 then
      484 else 485))) else (if i.val < 492 then (if i.val < 490 then 494 else (if i.val < 491
      then 491 else 496)) else (if i.val < 494 then (if i.val < 493 then 498 else 489) else (if
      i.val < 495 then 493 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 490 else (if i.val < 498 then 492 else 497)) else (if i.val < 500 then 519 else
      (if i.val < 501 then 521 else 520))) else (if i.val < 505 then (if i.val < 503 then 522
      else (if i.val < 504 then 506 else 508)) else (if i.val < 507 then (if i.val < 506 then
      507 else 529) else (if i.val < 508 then 531 else 530))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 538 else (if i.val < 511 then 540 else 539)) else (if i.val < 513 then 541 else
      (if i.val < 514 then 542 else 543))) else (if i.val < 518 then (if i.val < 516 then 499
      else (if i.val < 517 then 501 else 500)) else (if i.val < 519 then 502 else (if i.val <
      520 then 515 else 516)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 517 else (if i.val < 523 then 518 else 523)) else (if i.val < 525 then 526 else (if
      i.val < 526 then 524 else 525))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 503)) else (if i.val < 532 then (if i.val < 531 then 504
      else 505) else (if i.val < 533 then 509 else 512))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 510 else (if i.val < 536 then 511
      else 513)) else (if i.val < 538 then 514 else (if i.val < 539 then 532 else 535))) else
      (if i.val < 543 then (if i.val < 541 then 534 else (if i.val < 542 then 533 else 536))
      else (if i.val < 545 then (if i.val < 544 then 537 else 547) else (if i.val < 546 then 545
      else 544)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 546 else
      (if i.val < 549 then 549 else 569)) else (if i.val < 551 then 574 else (if i.val < 552
      then 575 else 577))) else (if i.val < 556 then (if i.val < 554 then 576 else (if i.val <
      555 then 556 else 554)) else (if i.val < 558 then (if i.val < 557 then 555 else 561) else
      (if i.val < 559 then 562 else 564)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 563 else (if i.val < 562 then
      583 else 582)) else (if i.val < 564 then 585 else (if i.val < 565 then 584 else 591)))
      else (if i.val < 569 then (if i.val < 567 then 590 else (if i.val < 568 then 592 else
      593)) else (if i.val < 570 then 548 else (if i.val < 571 then 551 else 550)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 553 else (if i.val < 574 then
      552 else 571)) else (if i.val < 576 then 570 else (if i.val < 577 then 572 else 573)))
      else (if i.val < 581 then (if i.val < 579 then 580 else (if i.val < 580 then 578 else
      579)) else (if i.val < 583 then (if i.val < 582 then 581 else 558) else (if i.val < 584
      then 557 else 559))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 560 else (if i.val < 587 then 567 else 565)) else (if i.val < 589
      then 566 else (if i.val < 590 then 568 else 588))) else (if i.val < 594 then (if i.val <
      592 then 587 else (if i.val < 593 then 586 else 589)) else (if i.val < 596 then (if i.val
      < 595 then 597 else 595) else (if i.val < 597 then 594 else 596)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 601 else (if i.val < 600 then 599 else
      598)) else (if i.val < 602 then 600 else (if i.val < 603 then 606 else 609))) else (if
      i.val < 607 then (if i.val < 605 then 608 else (if i.val < 606 then 607 else 630)) else
      (if i.val < 609 then (if i.val < 608 then 633 else 631) else (if i.val < 610 then 632 else
      638)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 639 else (if
      i.val < 613 then 641 else 640)) else (if i.val < 615 then 614 else (if i.val < 616 then
      617 else 615))) else (if i.val < 620 then (if i.val < 618 then 616 else (if i.val < 619
      then 622 else 623)) else (if i.val < 621 then 625 else (if i.val < 622 then 624 else
      647)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 646 else (if
      i.val < 625 then 649 else 648)) else (if i.val < 627 then 655 else (if i.val < 628 then
      654 else 656))) else (if i.val < 632 then (if i.val < 630 then 657 else (if i.val < 631
      then 602 else 604)) else (if i.val < 634 then (if i.val < 633 then 603 else 605) else (if
      i.val < 635 then 611 else 610))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 613 else (if i.val < 638 then 612 else 635)) else
      (if i.val < 640 then 634 else (if i.val < 641 then 636 else 637))) else (if i.val < 645
      then (if i.val < 643 then 644 else (if i.val < 644 then 642 else 643)) else (if i.val <
      647 then (if i.val < 646 then 645 else 619) else (if i.val < 648 then 618 else 620))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 621 else (if i.val <
      651 then 628 else 626)) else (if i.val < 653 then 627 else (if i.val < 654 then 629 else
      652))) else (if i.val < 658 then (if i.val < 656 then 651 else (if i.val < 657 then 650
      else 653)) else (if i.val < 660 then (if i.val < 659 then 661 else 659) else (if i.val <
      661 then 658 else 660)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 746 else (if i.val < 664 then 745 else
      683)) else (if i.val < 666 then 747 else (if i.val < 667 then 748 else 751))) else (if
      i.val < 671 then (if i.val < 669 then 752 else (if i.val < 670 then 749 else 750)) else
      (if i.val < 672 then 753 else (if i.val < 673 then 754 else 755)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 756 else (if i.val < 676 then 759 else
      760)) else (if i.val < 678 then 757 else (if i.val < 679 then 758 else 761))) else (if
      i.val < 683 then (if i.val < 681 then 762 else (if i.val < 682 then 701 else 700)) else
      (if i.val < 685 then (if i.val < 684 then 702 else 703) else (if i.val < 686 then 704 else
      707))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 708 else (if i.val < 689 then 705 else 706)) else (if i.val < 691 then 709 else
      (if i.val < 692 then 710 else 711))) else (if i.val < 696 then (if i.val < 694 then 712
      else (if i.val < 695 then 715 else 716)) else (if i.val < 698 then (if i.val < 697 then
      713 else 714) else (if i.val < 699 then 717 else 718)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 772 else (if i.val < 702 then 771 else 664)) else
      (if i.val < 704 then 773 else (if i.val < 705 then 774 else 777))) else (if i.val < 709
      then (if i.val < 707 then 778 else (if i.val < 708 then 775 else 776)) else (if i.val <
      711 then (if i.val < 710 then 779 else 780) else (if i.val < 712 then 781 else 782)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 785 else (if i.val < 715 then 786 else 783))
      else (if i.val < 717 then 784 else (if i.val < 718 then 787 else 788))) else (if i.val <
      722 then (if i.val < 720 then 797 else (if i.val < 721 then 798 else 799)) else (if i.val
      < 723 then 800 else (if i.val < 724 then 801 else 802)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 803 else (if i.val < 727 then 804 else 663)) else
      (if i.val < 729 then 662 else (if i.val < 730 then 665 else 666))) else (if i.val < 734
      then (if i.val < 732 then 669 else (if i.val < 733 then 670 else 667)) else (if i.val <
      736 then (if i.val < 735 then 668 else 671) else (if i.val < 737 then 672 else 673)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      674 else (if i.val < 740 then 677 else 678)) else (if i.val < 742 then 675 else (if i.val
      < 743 then 676 else 679))) else (if i.val < 747 then (if i.val < 745 then 680 else (if
      i.val < 746 then 727 else 728)) else (if i.val < 749 then (if i.val < 748 then 729 else
      730) else (if i.val < 750 then 731 else 732)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 733 else (if i.val < 753 then 734 else 735)) else (if i.val <
      755 then 736 else (if i.val < 756 then 737 else 738))) else (if i.val < 760 then (if i.val
      < 758 then 739 else (if i.val < 759 then 740 else 741)) else (if i.val < 762 then (if
      i.val < 761 then 742 else 743) else (if i.val < 763 then 744 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 681 else 682)) else (if i.val < 774 then 684 else (if i.val < 775
      then 685 else 686)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      687 else (if i.val < 778 then 688 else 689)) else (if i.val < 780 then 690 else (if i.val
      < 781 then 691 else 692))) else (if i.val < 785 then (if i.val < 783 then 693 else (if
      i.val < 784 then 694 else 695)) else (if i.val < 787 then (if i.val < 786 then 696 else
      697) else (if i.val < 788 then 698 else 699))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 719 else (if i.val < 791 then 720 else
      721)) else (if i.val < 793 then 722 else (if i.val < 794 then 723 else 724))) else (if
      i.val < 798 then (if i.val < 796 then 725 else (if i.val < 797 then 726 else 789)) else
      (if i.val < 800 then (if i.val < 799 then 790 else 791) else (if i.val < 801 then 792 else
      793)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 794 else (if
      i.val < 804 then 795 else 796)) else (if i.val < 806 then 810 else (if i.val < 807 then
      807 else 812))) else (if i.val < 811 then (if i.val < 809 then 814 else (if i.val < 810
      then 805 else 809)) else (if i.val < 813 then (if i.val < 812 then 811 else 806) else (if
      i.val < 814 then 808 else 813)))))))))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed vertex, edge and branch bijections for this frame permutation. -/
def hint4 : Fin 815 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
    (if i.val < 25 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 37 then ⟨[0, 1], [0], [false]⟩
    else (if i.val < 43 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 46 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 48 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))))) else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53
    then (if i.val < 51 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 52 then ⟨[0,
    1, 2], [0, 1], [false, false]⟩ else ⟨[1, 0, 2], [1, 0], [false, false]⟩)) else (if i.val <
    54 then ⟨[1, 0, 2], [1, 0], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else
    (if i.val < 59 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 60 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else (if i.val < 61 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else
    ⟨[1, 0, 2], [1, 0], [false, false]⟩)))) else (if i.val < 68 then (if i.val < 65 then (if
    i.val < 63 then ⟨[1, 0, 2], [1, 0], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩) else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩)) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else (if i.val < 105 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val
    < 106 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩))) else (if i.val < 110 then (if i.val < 108 then ⟨[0, 1, 2, 3], [0, 1, 2], [false,
    false, false]⟩ else (if i.val < 109 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false, false]⟩
    else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else (if i.val < 111 then ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 112 then ⟨[1, 0, 2, 3], [1, 0, 2],
    [false, false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)))) else (if
    i.val < 119 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 122 then
    (if i.val < 120 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 121
    then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩)) else ⟨[0, 1, 2], [0, 1], [false, false]⟩))) else (if i.val < 139 then (if i.val <
    132 then (if i.val < 129 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 130 then
    ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 2, 1], [0, 1], [false, true]⟩)) else ⟨[0, 2,
    1], [0, 1], [false, true]⟩) else (if i.val < 145 then (if i.val < 142 then (if i.val < 140
    then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0,
    1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2], [0, 1], [false, false]⟩))) else (if i.val <
    177 then (if i.val < 164 then (if i.val < 158 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else
    (if i.val < 161 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 162 then ⟨[0, 1,
    2], [0, 1], [false, false]⟩ else ⟨[0, 2, 1], [0, 1], [false, true]⟩))) else (if i.val < 170
    then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else ⟨[0,
    1, 2], [0, 1], [false, false]⟩))) else (if i.val < 305 then (if i.val < 254 then (if i.val <
    228 then (if i.val < 215 then (if i.val < 209 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else
    (if i.val < 212 then (if i.val < 210 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 2,
    1], [0, 1], [false, true]⟩) else ⟨[0, 2, 1], [0, 1], [false, true]⟩)) else (if i.val < 221
    then (if i.val < 218 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else (if i.val < 219 then ⟨[0,
    2, 1], [0, 1], [false, true]⟩ else (if i.val < 220 then ⟨[0, 2, 1], [0, 1], [false, true]⟩
    else ⟨[0, 1, 2], [0, 1], [false, false]⟩))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else
    (if i.val < 241 then (if i.val < 234 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val
    < 237 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 239 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else (if i.val < 240 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 2,
    1], [0, 1], [false, true]⟩)))) else (if i.val < 247 then ⟨[0, 2, 1], [0, 1], [false, true]⟩
    else (if i.val < 250 then (if i.val < 248 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else ⟨[0,
    1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)))) else ⟨[0, 1,
    2], [0, 1], [false, false]⟩) else (if i.val < 356 then (if i.val < 330 then (if i.val < 317
    then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 323 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩)) else (if i.val < 343 then ⟨[2, 1,
    0], [1, 0], [true, true]⟩ else (if i.val < 349 then (if i.val < 346 then (if i.val < 344
    then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0,
    1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2], [0, 1], [false, false]⟩))) else (if i.val <
    381 then (if i.val < 368 then (if i.val < 362 then (if i.val < 359 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else (if i.val < 360 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val
    < 361 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩)))
    else (if i.val < 365 then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else (if i.val < 366 then ⟨[2,
    1, 0], [1, 0], [true, true]⟩ else (if i.val < 367 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else ⟨[2, 1, 0], [1, 0], [true, true]⟩)))) else (if i.val < 374 then ⟨[2, 1, 0], [1, 0],
    [true, true]⟩ else (if i.val < 377 then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 394 then (if i.val < 387 then (if
    i.val < 384 then (if i.val < 382 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false, false]⟩ else
    (if i.val < 383 then ⟨[1, 0, 3, 2], [1, 0, 2], [false, false, true]⟩ else ⟨[0, 1, 2, 3], [0,
    1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else
    (if i.val < 390 then (if i.val < 388 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩
    else (if i.val < 389 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false, false]⟩ else ⟨[1, 0, 3,
    2], [1, 0, 2], [false, false, true]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩))))) else (if i.val < 611
    then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 425 then ⟨[0, 1, 2, 3],
    [0, 1, 2], [false, false, false]⟩ else (if i.val < 428 then (if i.val < 426 then ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 427 then ⟨[0, 3, 2, 1], [0, 2, 1],
    [false, true, true]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 445 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 451 then (if i.val < 448 then (if i.val < 446 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 447 then ⟨[0, 3, 2, 1],
    [0, 2, 1], [false, true, true]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1, 2, 3], [0, 1, 2], [false,
    false, false]⟩))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then ⟨[0,
    1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 467 then ⟨[0, 1, 2, 3], [0, 1,
    2], [false, false, false]⟩ else (if i.val < 468 then ⟨[0, 1, 2, 3], [0, 1, 2], [false,
    false, false]⟩ else (if i.val < 469 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩
    else ⟨[0, 3, 2, 1], [0, 2, 1], [false, true, true]⟩)))) else (if i.val < 476 then ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 479 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 481 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩ else (if i.val < 482 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0,
    3, 2, 1], [0, 2, 1], [false, true, true]⟩))))) else (if i.val < 496 then (if i.val < 489
    then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩) else (if i.val < 502 then (if i.val < 499 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else ⟨[0, 1], [0, 1], [false, false]⟩) else ⟨[0, 1], [0, 1], [false, false]⟩)))) else ⟨[0,
    1], [0, 1], [false, false]⟩) else (if i.val < 713 then (if i.val < 662 then ⟨[0, 1], [0, 1],
    [false, false]⟩ else (if i.val < 687 then (if i.val < 674 then (if i.val < 668 then (if
    i.val < 665 then (if i.val < 663 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if
    i.val < 664 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 0, 2], [0, 2, 1],
    [false, false, false]⟩)) else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1,
    2], [0, 1, 2], [false, false, false]⟩) else (if i.val < 680 then ⟨[0, 1, 2], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 683 then ⟨[0, 1, 2], [0, 1, 2], [false, false,
    false]⟩ else (if i.val < 685 then (if i.val < 684 then ⟨[1, 0, 2], [0, 2, 1], [false, false,
    false]⟩ else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1, 2], [0, 1, 2],
    [false, false, false]⟩)))) else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩)) else (if
    i.val < 764 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 789 then
    ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 802 then ⟨[0, 1, 2], [0, 1,
    2], [false, false, false]⟩ else (if i.val < 808 then (if i.val < 805 then ⟨[0, 1, 2], [0, 1,
    2], [false, false, false]⟩ else ⟨[0, 1], [0, 1, 2], [false, false, false]⟩) else ⟨[0, 1],
    [0, 1, 2], [false, false, false]⟩))))))))

/-- The kernel checks the supplied bijections without repeating permutation search. -/
theorem hints_valid4 : ∀ i, (hint4 i).check ((L24Graphs.graph i).relabel labels4)
    (L24Graphs.graph (destination4 i)) = true := by
  decide +kernel

/-- Every column is transported as a full decorated labelled graph. -/
theorem covered4 : ∀ i, ((L24Graphs.graph i).relabel labels4).isomorphic?
    (L24Graphs.graph (destination4 i)) = true := by
  intro i
  exact (hint4 i).check_sound _ _ (hints_valid4 i)

/-- The 5-th permutation of the three free markings; old labels map covariantly. -/
def labels5 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 2, 0]
  invFun := ![3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A candidate bijection of the held frame columns. -/
def destination5 : Equiv.Perm (Fin 815) where
  toFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 20 else (if i.val < 2 then 22 else 19)) else (if i.val < 4 then 21 else (if i.val <
      5 then 33 else 32))) else (if i.val < 9 then (if i.val < 7 then 31 else (if i.val < 8 then
      9 else 8)) else (if i.val < 10 then 7 else (if i.val < 11 then 40 else 41)))) else (if
      i.val < 18 then (if i.val < 15 then (if i.val < 13 then 39 else (if i.val < 14 then 42
      else 43)) else (if i.val < 16 then 15 else (if i.val < 17 then 16 else 17))) else (if
      i.val < 21 then (if i.val < 19 then 18 else (if i.val < 20 then 2 else 0)) else (if i.val
      < 23 then (if i.val < 22 then 3 else 1) else (if i.val < 24 then 27 else 28))))) else (if
      i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 25 else (if
      i.val < 27 then 26 else 23)) else (if i.val < 29 then 24 else (if i.val < 30 then 29 else
      30))) else (if i.val < 34 then (if i.val < 32 then 6 else (if i.val < 33 then 5 else 4))
      else (if i.val < 35 then 36 else (if i.val < 36 then 35 else 34)))) else (if i.val < 43
      then (if i.val < 40 then (if i.val < 38 then 37 else (if i.val < 39 then 38 else 12)) else
      (if i.val < 41 then 10 else (if i.val < 42 then 11 else 13))) else (if i.val < 46 then (if
      i.val < 44 then 14 else (if i.val < 45 then 47 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 46 else 44) else (if i.val < 49 then 84 else 85)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 82
      else (if i.val < 52 then 83 else 62)) else (if i.val < 54 then 61 else (if i.val < 55 then
      87 else 86))) else (if i.val < 59 then (if i.val < 57 then 88 else (if i.val < 58 then 95
      else 96)) else (if i.val < 60 then 93 else (if i.val < 61 then 94 else 53)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 52 else (if i.val < 64 then 97
      else 66)) else (if i.val < 66 then 67 else (if i.val < 67 then 64 else 65))) else (if
      i.val < 71 then (if i.val < 69 then 68 else (if i.val < 70 then 69 else 70)) else (if
      i.val < 73 then (if i.val < 72 then 103 else 104) else (if i.val < 74 then 102 else
      105))))) else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76
      then 75 else (if i.val < 77 then 76 else 77)) else (if i.val < 79 then 78 else (if i.val <
      80 then 79 else 80))) else (if i.val < 84 then (if i.val < 82 then 81 else (if i.val < 83
      then 50 else 51)) else (if i.val < 86 then (if i.val < 85 then 48 else 49) else (if i.val
      < 87 then 55 else 54)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then
      56 else (if i.val < 90 then 91 else 90)) else (if i.val < 92 then 89 else (if i.val < 93
      then 92 else 59))) else (if i.val < 97 then (if i.val < 95 then 60 else (if i.val < 96
      then 57 else 58)) else (if i.val < 99 then (if i.val < 98 then 63 else 100) else (if i.val
      < 100 then 99 else 98))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val <
      113 then (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 101 else (if i.val
      < 103 then 73 else 71)) else (if i.val < 105 then 72 else (if i.val < 106 then 74 else
      118))) else (if i.val < 110 then (if i.val < 108 then 117 else (if i.val < 109 then 111
      else 120)) else (if i.val < 111 then 119 else (if i.val < 112 then 108 else 113)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 112 else (if i.val < 115
      then 114 else 115)) else (if i.val < 117 then 116 else (if i.val < 118 then 107 else
      106))) else (if i.val < 122 then (if i.val < 120 then 110 else (if i.val < 121 then 109
      else 202)) else (if i.val < 124 then (if i.val < 123 then 201 else 203) else (if i.val <
      125 then 204 else 205))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 206 else (if i.val < 128 then 208 else 207)) else (if i.val <
      130 then 209 else (if i.val < 131 then 218 else 219))) else (if i.val < 135 then (if i.val
      < 133 then 215 else (if i.val < 134 then 216 else 217)) else (if i.val < 137 then (if
      i.val < 136 then 212 else 213) else (if i.val < 138 then 214 else 210)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 211 else (if i.val < 141 then 234 else
      233)) else (if i.val < 143 then 235 else (if i.val < 144 then 236 else 238))) else (if
      i.val < 148 then (if i.val < 146 then 237 else (if i.val < 147 then 239 else 246)) else
      (if i.val < 150 then (if i.val < 149 then 247 else 244) else (if i.val < 151 then 245 else
      242)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 243 else (if i.val < 154 then 240 else 241)) else (if i.val
      < 156 then 156 else (if i.val < 157 then 155 else 157))) else (if i.val < 161 then (if
      i.val < 159 then 158 else (if i.val < 160 then 160 else 159)) else (if i.val < 162 then
      161 else (if i.val < 163 then 168 else 169)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 166 else (if i.val < 166 then 167 else 164)) else (if i.val <
      168 then 165 else (if i.val < 169 then 162 else 163))) else (if i.val < 173 then (if i.val
      < 171 then 261 else (if i.val < 172 then 262 else 260)) else (if i.val < 175 then (if
      i.val < 174 then 263 else 264) else (if i.val < 176 then 265 else 267))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 266 else (if
      i.val < 179 then 268 else 269)) else (if i.val < 181 then 270 else (if i.val < 182 then
      271 else 182))) else (if i.val < 186 then (if i.val < 184 then 183 else (if i.val < 185
      then 184 else 185)) else (if i.val < 188 then (if i.val < 187 then 186 else 187) else (if
      i.val < 189 then 188 else 189)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 190 else (if i.val < 192 then 191 else 192)) else (if i.val < 194 then 193 else
      (if i.val < 195 then 194 else 195))) else (if i.val < 199 then (if i.val < 197 then 196
      else (if i.val < 198 then 197 else 198)) else (if i.val < 201 then (if i.val < 200 then
      199 else 200) else (if i.val < 202 then 122 else 121)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 123 else (if i.val < 205 then 124 else 125)) else (if
      i.val < 207 then 126 else (if i.val < 208 then 128 else 127))) else (if i.val < 212 then
      (if i.val < 210 then 129 else (if i.val < 211 then 138 else 139)) else (if i.val < 213
      then 135 else (if i.val < 214 then 136 else 137)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 132 else (if i.val < 217 then 133 else 134)) else (if i.val
      < 219 then 130 else (if i.val < 220 then 131 else 222))) else (if i.val < 224 then (if
      i.val < 222 then 221 else (if i.val < 223 then 220 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 228 else 227))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 226 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 141))) else (if i.val < 237 then (if i.val < 235 then 140 else (if i.val <
      236 then 142 else 143)) else (if i.val < 239 then (if i.val < 238 then 145 else 144) else
      (if i.val < 240 then 146 else 153)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 154 else (if i.val < 243 then 151 else 152)) else (if i.val < 245 then
      149 else (if i.val < 246 then 150 else 147))) else (if i.val < 250 then (if i.val < 248
      then 148 else (if i.val < 249 then 250 else 249)) else (if i.val < 252 then (if i.val <
      251 then 248 else 251) else (if i.val < 253 then 252 else 253)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      255 else (if i.val < 256 then 254 else 256)) else (if i.val < 258 then 257 else (if i.val
      < 259 then 258 else 259))) else (if i.val < 263 then (if i.val < 261 then 172 else (if
      i.val < 262 then 170 else 171)) else (if i.val < 264 then 173 else (if i.val < 265 then
      174 else 175)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 177
      else (if i.val < 268 then 176 else 178)) else (if i.val < 270 then 179 else (if i.val <
      271 then 180 else 181))) else (if i.val < 275 then (if i.val < 273 then 275 else (if i.val
      < 274 then 273 else 274)) else (if i.val < 277 then (if i.val < 276 then 272 else 295)
      else (if i.val < 278 then 277 else 301))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 300 else (if i.val < 281 then 303 else 302))
      else (if i.val < 283 then 284 else (if i.val < 284 then 283 else 282))) else (if i.val <
      288 then (if i.val < 286 then 308 else (if i.val < 287 then 310 else 309)) else (if i.val
      < 290 then (if i.val < 289 then 288 else 290) else (if i.val < 291 then 289 else 316))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 317 else (if i.val <
      294 then 315 else 318)) else (if i.val < 296 then 276 else (if i.val < 297 then 297 else
      296))) else (if i.val < 301 then (if i.val < 299 then 298 else (if i.val < 300 then 299
      else 279)) else (if i.val < 303 then (if i.val < 302 then 278 else 281) else (if i.val <
      304 then 280 else 306))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 305 else (if i.val
      < 307 then 304 else 307)) else (if i.val < 309 then 285 else (if i.val < 310 then 287 else
      286))) else (if i.val < 314 then (if i.val < 312 then 313 else (if i.val < 313 then 312
      else 311)) else (if i.val < 315 then 314 else (if i.val < 316 then 293 else 291)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 292 else (if i.val < 319
      then 294 else 322)) else (if i.val < 321 then 320 else (if i.val < 322 then 321 else
      319))) else (if i.val < 326 then (if i.val < 324 then 373 else (if i.val < 325 then 372
      else 371)) else (if i.val < 328 then (if i.val < 327 then 363 else 362) else (if i.val <
      329 then 361 else 332))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 330 else (if i.val < 332 then 331 else 329)) else (if i.val <
      334 then 376 else (if i.val < 335 then 374 else 375))) else (if i.val < 339 then (if i.val
      < 337 then 370 else (if i.val < 338 then 369 else 368)) else (if i.val < 341 then (if
      i.val < 340 then 367 else 353) else (if i.val < 342 then 352 else 351)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 350 else (if i.val < 345 then 354 else
      356)) else (if i.val < 347 then 355 else (if i.val < 348 then 347 else 349))) else (if
      i.val < 352 then (if i.val < 350 then 348 else (if i.val < 351 then 343 else 342)) else
      (if i.val < 354 then (if i.val < 353 then 341 else 340) else (if i.val < 355 then 344 else
      346)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 345 else (if i.val < 358 then 357 else 359)) else (if i.val
      < 360 then 358 else (if i.val < 361 then 360 else 328))) else (if i.val < 365 then (if
      i.val < 363 then 327 else (if i.val < 364 then 326 else 365)) else (if i.val < 366 then
      364 else (if i.val < 367 then 366 else 339)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 338 else (if i.val < 370 then 337 else 336)) else (if i.val <
      372 then 325 else (if i.val < 373 then 324 else 323))) else (if i.val < 377 then (if i.val
      < 375 then 334 else (if i.val < 376 then 335 else 333)) else (if i.val < 379 then (if
      i.val < 378 then 406 else 407) else (if i.val < 380 then 404 else 405))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 388 else (if
      i.val < 383 then 389 else 408)) else (if i.val < 385 then 412 else (if i.val < 386 then
      413 else 410))) else (if i.val < 390 then (if i.val < 388 then 411 else (if i.val < 389
      then 381 else 382)) else (if i.val < 392 then (if i.val < 391 then 414 else 393) else (if
      i.val < 393 then 394 else 391)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 392 else (if i.val < 396 then 395 else 396)) else (if i.val < 398 then 397 else
      (if i.val < 399 then 416 else 399))) else (if i.val < 403 then (if i.val < 401 then 400
      else (if i.val < 402 then 401 else 402)) else (if i.val < 405 then (if i.val < 404 then
      403 else 379) else (if i.val < 406 then 380 else 377))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 378 else (if i.val < 409 then
      383 else 409)) else (if i.val < 411 then 386 else (if i.val < 412 then 387 else 384)))
      else (if i.val < 416 then (if i.val < 414 then 385 else (if i.val < 415 then 390 else
      415)) else (if i.val < 417 then 398 else (if i.val < 418 then 460 else 463)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 464 else (if i.val < 421 then
      461 else 462)) else (if i.val < 423 then 465 else (if i.val < 424 then 466 else 468)))
      else (if i.val < 428 then (if i.val < 426 then 467 else (if i.val < 427 then 469 else
      473)) else (if i.val < 430 then (if i.val < 429 then 476 else 477) else (if i.val < 431
      then 474 else 475))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 478 else (if i.val < 434 then 479 else 481)) else (if i.val < 436
      then 480 else (if i.val < 437 then 482 else 437))) else (if i.val < 441 then (if i.val <
      439 then 440 else (if i.val < 440 then 441 else 438)) else (if i.val < 443 then (if i.val
      < 442 then 439 else 442) else (if i.val < 444 then 443 else 445)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 444 else (if i.val < 447 then 446 else
      486)) else (if i.val < 449 then 487 else (if i.val < 450 then 488 else 450))) else (if
      i.val < 454 then (if i.val < 452 then 451 else (if i.val < 453 then 452 else 453)) else
      (if i.val < 456 then (if i.val < 455 then 454 else 455) else (if i.val < 457 then 456 else
      457)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 458 else (if i.val < 460 then 459 else 417)) else (if i.val
      < 462 then 420 else (if i.val < 463 then 421 else 418))) else (if i.val < 467 then (if
      i.val < 465 then 419 else (if i.val < 466 then 422 else 423)) else (if i.val < 468 then
      425 else (if i.val < 469 then 424 else 426)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 427 else (if i.val < 475 then 430 else 431))) else (if i.val < 479 then (if i.val
      < 477 then 428 else (if i.val < 478 then 429 else 432)) else (if i.val < 481 then (if
      i.val < 480 then 433 else 435) else (if i.val < 482 then 434 else 436))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 483 else (if
      i.val < 485 then 484 else 485)) else (if i.val < 487 then 447 else (if i.val < 488 then
      448 else 449))) else (if i.val < 492 then (if i.val < 490 then 494 else (if i.val < 491
      then 496 else 491)) else (if i.val < 494 then (if i.val < 493 then 498 else 493) else (if
      i.val < 495 then 489 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 490 else (if i.val < 498 then 497 else 492)) else (if i.val < 500 then 519 else
      (if i.val < 501 then 521 else 520))) else (if i.val < 505 then (if i.val < 503 then 522
      else (if i.val < 504 then 529 else 531)) else (if i.val < 507 then (if i.val < 506 then
      530 else 506) else (if i.val < 508 then 508 else 507))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 538 else (if i.val < 511 then 540 else 541)) else (if i.val < 513 then 539 else
      (if i.val < 514 then 542 else 543))) else (if i.val < 518 then (if i.val < 516 then 515
      else (if i.val < 517 then 516 else 517)) else (if i.val < 519 then 518 else (if i.val <
      520 then 499 else 501)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 500 else (if i.val < 523 then 502 else 523)) else (if i.val < 525 then 526 else (if
      i.val < 526 then 525 else 524))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 503)) else (if i.val < 532 then (if i.val < 531 then 505
      else 504) else (if i.val < 533 then 532 else 535))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 534 else (if i.val < 536 then 533
      else 536)) else (if i.val < 538 then 537 else (if i.val < 539 then 509 else 512))) else
      (if i.val < 543 then (if i.val < 541 then 510 else (if i.val < 542 then 511 else 513))
      else (if i.val < 545 then (if i.val < 544 then 514 else 547) else (if i.val < 546 then 545
      else 546)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 544 else
      (if i.val < 549 then 569 else 549)) else (if i.val < 551 then 575 else (if i.val < 552
      then 574 else 577))) else (if i.val < 556 then (if i.val < 554 then 576 else (if i.val <
      555 then 556 else 555)) else (if i.val < 558 then (if i.val < 557 then 554 else 583) else
      (if i.val < 559 then 582 else 585)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 584 else (if i.val < 562 then
      561 else 562)) else (if i.val < 564 then 564 else (if i.val < 565 then 563 else 591)))
      else (if i.val < 569 then (if i.val < 567 then 592 else (if i.val < 568 then 590 else
      593)) else (if i.val < 570 then 548 else (if i.val < 571 then 571 else 570)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 572 else (if i.val < 574 then
      573 else 551)) else (if i.val < 576 then 550 else (if i.val < 577 then 553 else 552)))
      else (if i.val < 581 then (if i.val < 579 then 580 else (if i.val < 580 then 579 else
      578)) else (if i.val < 583 then (if i.val < 582 then 581 else 558) else (if i.val < 584
      then 557 else 560))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 559 else (if i.val < 587 then 588 else 587)) else (if i.val < 589
      then 586 else (if i.val < 590 then 589 else 567))) else (if i.val < 594 then (if i.val <
      592 then 565 else (if i.val < 593 then 566 else 568)) else (if i.val < 596 then (if i.val
      < 595 then 597 else 595) else (if i.val < 597 then 596 else 594)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 601 else (if i.val < 600 then 599 else
      600)) else (if i.val < 602 then 598 else (if i.val < 603 then 630 else 633))) else (if
      i.val < 607 then (if i.val < 605 then 631 else (if i.val < 606 then 632 else 606)) else
      (if i.val < 609 then (if i.val < 608 then 609 else 608) else (if i.val < 610 then 607 else
      639)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 638 else (if
      i.val < 613 then 641 else 640)) else (if i.val < 615 then 614 else (if i.val < 616 then
      617 else 616))) else (if i.val < 620 then (if i.val < 618 then 615 else (if i.val < 619
      then 647 else 646)) else (if i.val < 621 then 649 else (if i.val < 622 then 648 else
      622)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 623 else (if
      i.val < 625 then 625 else 624)) else (if i.val < 627 then 655 else (if i.val < 628 then
      656 else 654))) else (if i.val < 632 then (if i.val < 630 then 657 else (if i.val < 631
      then 602 else 604)) else (if i.val < 634 then (if i.val < 633 then 605 else 603) else (if
      i.val < 635 then 635 else 634))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 636 else (if i.val < 638 then 637 else 611)) else
      (if i.val < 640 then 610 else (if i.val < 641 then 613 else 612))) else (if i.val < 645
      then (if i.val < 643 then 644 else (if i.val < 644 then 643 else 642)) else (if i.val <
      647 then (if i.val < 646 then 645 else 619) else (if i.val < 648 then 618 else 621))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 620 else (if i.val <
      651 then 652 else 651)) else (if i.val < 653 then 650 else (if i.val < 654 then 653 else
      628))) else (if i.val < 658 then (if i.val < 656 then 626 else (if i.val < 657 then 627
      else 629)) else (if i.val < 660 then (if i.val < 659 then 661 else 659) else (if i.val <
      661 then 660 else 658)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 746 else (if i.val < 664 then 745 else
      683)) else (if i.val < 666 then 747 else (if i.val < 667 then 748 else 751))) else (if
      i.val < 671 then (if i.val < 669 then 752 else (if i.val < 670 then 749 else 750)) else
      (if i.val < 672 then 753 else (if i.val < 673 then 754 else 755)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 756 else (if i.val < 676 then 759 else
      760)) else (if i.val < 678 then 757 else (if i.val < 679 then 758 else 761))) else (if
      i.val < 683 then (if i.val < 681 then 762 else (if i.val < 682 then 772 else 771)) else
      (if i.val < 685 then (if i.val < 684 then 664 else 773) else (if i.val < 686 then 774 else
      777))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 778 else (if i.val < 689 then 775 else 776)) else (if i.val < 691 then 779 else
      (if i.val < 692 then 780 else 781))) else (if i.val < 696 then (if i.val < 694 then 782
      else (if i.val < 695 then 785 else 786)) else (if i.val < 698 then (if i.val < 697 then
      783 else 784) else (if i.val < 699 then 787 else 788)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 701 else (if i.val < 702 then 700 else 702)) else
      (if i.val < 704 then 703 else (if i.val < 705 then 704 else 707))) else (if i.val < 709
      then (if i.val < 707 then 708 else (if i.val < 708 then 705 else 706)) else (if i.val <
      711 then (if i.val < 710 then 709 else 710) else (if i.val < 712 then 711 else 712)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 715 else (if i.val < 715 then 716 else 713))
      else (if i.val < 717 then 714 else (if i.val < 718 then 717 else 718))) else (if i.val <
      722 then (if i.val < 720 then 797 else (if i.val < 721 then 798 else 799)) else (if i.val
      < 723 then 800 else (if i.val < 724 then 801 else 802)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 803 else (if i.val < 727 then 804 else 727)) else
      (if i.val < 729 then 728 else (if i.val < 730 then 729 else 730))) else (if i.val < 734
      then (if i.val < 732 then 731 else (if i.val < 733 then 732 else 733)) else (if i.val <
      736 then (if i.val < 735 then 734 else 735) else (if i.val < 737 then 736 else 737)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      738 else (if i.val < 740 then 739 else 740)) else (if i.val < 742 then 741 else (if i.val
      < 743 then 742 else 743))) else (if i.val < 747 then (if i.val < 745 then 744 else (if
      i.val < 746 then 663 else 662)) else (if i.val < 749 then (if i.val < 748 then 665 else
      666) else (if i.val < 750 then 669 else 670)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 667 else (if i.val < 753 then 668 else 671)) else (if i.val <
      755 then 672 else (if i.val < 756 then 673 else 674))) else (if i.val < 760 then (if i.val
      < 758 then 677 else (if i.val < 759 then 678 else 675)) else (if i.val < 762 then (if
      i.val < 761 then 676 else 679) else (if i.val < 763 then 680 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 682 else 681)) else (if i.val < 774 then 684 else (if i.val < 775
      then 685 else 688)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      689 else (if i.val < 778 then 686 else 687)) else (if i.val < 780 then 690 else (if i.val
      < 781 then 691 else 692))) else (if i.val < 785 then (if i.val < 783 then 693 else (if
      i.val < 784 then 696 else 697)) else (if i.val < 787 then (if i.val < 786 then 694 else
      695) else (if i.val < 788 then 698 else 699))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 789 else (if i.val < 791 then 790 else
      791)) else (if i.val < 793 then 792 else (if i.val < 794 then 793 else 794))) else (if
      i.val < 798 then (if i.val < 796 then 795 else (if i.val < 797 then 796 else 719)) else
      (if i.val < 800 then (if i.val < 799 then 720 else 721) else (if i.val < 801 then 722 else
      723)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 724 else (if
      i.val < 804 then 725 else 726)) else (if i.val < 806 then 810 else (if i.val < 807 then
      812 else 807))) else (if i.val < 811 then (if i.val < 809 then 814 else (if i.val < 810
      then 809 else 805)) else (if i.val < 813 then (if i.val < 812 then 811 else 806) else (if
      i.val < 814 then 813 else 808)))))))))))
  invFun :=
    (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
      (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val <
      1 then 20 else (if i.val < 2 then 22 else 19)) else (if i.val < 4 then 21 else (if i.val <
      5 then 33 else 32))) else (if i.val < 9 then (if i.val < 7 then 31 else (if i.val < 8 then
      9 else 8)) else (if i.val < 10 then 7 else (if i.val < 11 then 40 else 41)))) else (if
      i.val < 18 then (if i.val < 15 then (if i.val < 13 then 39 else (if i.val < 14 then 42
      else 43)) else (if i.val < 16 then 15 else (if i.val < 17 then 16 else 17))) else (if
      i.val < 21 then (if i.val < 19 then 18 else (if i.val < 20 then 2 else 0)) else (if i.val
      < 23 then (if i.val < 22 then 3 else 1) else (if i.val < 24 then 27 else 28))))) else (if
      i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 25 else (if
      i.val < 27 then 26 else 23)) else (if i.val < 29 then 24 else (if i.val < 30 then 29 else
      30))) else (if i.val < 34 then (if i.val < 32 then 6 else (if i.val < 33 then 5 else 4))
      else (if i.val < 35 then 36 else (if i.val < 36 then 35 else 34)))) else (if i.val < 43
      then (if i.val < 40 then (if i.val < 38 then 37 else (if i.val < 39 then 38 else 12)) else
      (if i.val < 41 then 10 else (if i.val < 42 then 11 else 13))) else (if i.val < 46 then (if
      i.val < 44 then 14 else (if i.val < 45 then 47 else 45)) else (if i.val < 48 then (if
      i.val < 47 then 46 else 44) else (if i.val < 49 then 84 else 85)))))) else (if i.val < 75
      then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then 82
      else (if i.val < 52 then 83 else 62)) else (if i.val < 54 then 61 else (if i.val < 55 then
      87 else 86))) else (if i.val < 59 then (if i.val < 57 then 88 else (if i.val < 58 then 95
      else 96)) else (if i.val < 60 then 93 else (if i.val < 61 then 94 else 53)))) else (if
      i.val < 68 then (if i.val < 65 then (if i.val < 63 then 52 else (if i.val < 64 then 97
      else 66)) else (if i.val < 66 then 67 else (if i.val < 67 then 64 else 65))) else (if
      i.val < 71 then (if i.val < 69 then 68 else (if i.val < 70 then 69 else 70)) else (if
      i.val < 73 then (if i.val < 72 then 103 else 104) else (if i.val < 74 then 102 else
      105))))) else (if i.val < 88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76
      then 75 else (if i.val < 77 then 76 else 77)) else (if i.val < 79 then 78 else (if i.val <
      80 then 79 else 80))) else (if i.val < 84 then (if i.val < 82 then 81 else (if i.val < 83
      then 50 else 51)) else (if i.val < 86 then (if i.val < 85 then 48 else 49) else (if i.val
      < 87 then 55 else 54)))) else (if i.val < 94 then (if i.val < 91 then (if i.val < 89 then
      56 else (if i.val < 90 then 91 else 90)) else (if i.val < 92 then 89 else (if i.val < 93
      then 92 else 59))) else (if i.val < 97 then (if i.val < 95 then 60 else (if i.val < 96
      then 57 else 58)) else (if i.val < 99 then (if i.val < 98 then 63 else 100) else (if i.val
      < 100 then 99 else 98))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val <
      113 then (if i.val < 107 then (if i.val < 104 then (if i.val < 102 then 101 else (if i.val
      < 103 then 73 else 71)) else (if i.val < 105 then 72 else (if i.val < 106 then 74 else
      118))) else (if i.val < 110 then (if i.val < 108 then 117 else (if i.val < 109 then 111
      else 120)) else (if i.val < 111 then 119 else (if i.val < 112 then 108 else 113)))) else
      (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then 112 else (if i.val < 115
      then 114 else 115)) else (if i.val < 117 then 116 else (if i.val < 118 then 107 else
      106))) else (if i.val < 122 then (if i.val < 120 then 110 else (if i.val < 121 then 109
      else 202)) else (if i.val < 124 then (if i.val < 123 then 201 else 203) else (if i.val <
      125 then 204 else 205))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
      then (if i.val < 127 then 206 else (if i.val < 128 then 208 else 207)) else (if i.val <
      130 then 209 else (if i.val < 131 then 218 else 219))) else (if i.val < 135 then (if i.val
      < 133 then 215 else (if i.val < 134 then 216 else 217)) else (if i.val < 137 then (if
      i.val < 136 then 212 else 213) else (if i.val < 138 then 214 else 210)))) else (if i.val <
      145 then (if i.val < 142 then (if i.val < 140 then 211 else (if i.val < 141 then 234 else
      233)) else (if i.val < 143 then 235 else (if i.val < 144 then 236 else 238))) else (if
      i.val < 148 then (if i.val < 146 then 237 else (if i.val < 147 then 239 else 246)) else
      (if i.val < 150 then (if i.val < 149 then 247 else 244) else (if i.val < 151 then 245 else
      242)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val <
      155 then (if i.val < 153 then 243 else (if i.val < 154 then 240 else 241)) else (if i.val
      < 156 then 156 else (if i.val < 157 then 155 else 157))) else (if i.val < 161 then (if
      i.val < 159 then 158 else (if i.val < 160 then 160 else 159)) else (if i.val < 162 then
      161 else (if i.val < 163 then 168 else 169)))) else (if i.val < 170 then (if i.val < 167
      then (if i.val < 165 then 166 else (if i.val < 166 then 167 else 164)) else (if i.val <
      168 then 165 else (if i.val < 169 then 162 else 163))) else (if i.val < 173 then (if i.val
      < 171 then 261 else (if i.val < 172 then 262 else 260)) else (if i.val < 175 then (if
      i.val < 174 then 263 else 264) else (if i.val < 176 then 265 else 267))))) else (if i.val
      < 190 then (if i.val < 183 then (if i.val < 180 then (if i.val < 178 then 266 else (if
      i.val < 179 then 268 else 269)) else (if i.val < 181 then 270 else (if i.val < 182 then
      271 else 182))) else (if i.val < 186 then (if i.val < 184 then 183 else (if i.val < 185
      then 184 else 185)) else (if i.val < 188 then (if i.val < 187 then 186 else 187) else (if
      i.val < 189 then 188 else 189)))) else (if i.val < 196 then (if i.val < 193 then (if i.val
      < 191 then 190 else (if i.val < 192 then 191 else 192)) else (if i.val < 194 then 193 else
      (if i.val < 195 then 194 else 195))) else (if i.val < 199 then (if i.val < 197 then 196
      else (if i.val < 198 then 197 else 198)) else (if i.val < 201 then (if i.val < 200 then
      199 else 200) else (if i.val < 202 then 122 else 121)))))))) else (if i.val < 305 then (if
      i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val
      < 206 then (if i.val < 204 then 123 else (if i.val < 205 then 124 else 125)) else (if
      i.val < 207 then 126 else (if i.val < 208 then 128 else 127))) else (if i.val < 212 then
      (if i.val < 210 then 129 else (if i.val < 211 then 138 else 139)) else (if i.val < 213
      then 135 else (if i.val < 214 then 136 else 137)))) else (if i.val < 221 then (if i.val <
      218 then (if i.val < 216 then 132 else (if i.val < 217 then 133 else 134)) else (if i.val
      < 219 then 130 else (if i.val < 220 then 131 else 222))) else (if i.val < 224 then (if
      i.val < 222 then 221 else (if i.val < 223 then 220 else 223)) else (if i.val < 226 then
      (if i.val < 225 then 224 else 225) else (if i.val < 227 then 228 else 227))))) else (if
      i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 226 else
      (if i.val < 230 then 229 else 230)) else (if i.val < 232 then 231 else (if i.val < 233
      then 232 else 141))) else (if i.val < 237 then (if i.val < 235 then 140 else (if i.val <
      236 then 142 else 143)) else (if i.val < 239 then (if i.val < 238 then 145 else 144) else
      (if i.val < 240 then 146 else 153)))) else (if i.val < 247 then (if i.val < 244 then (if
      i.val < 242 then 154 else (if i.val < 243 then 151 else 152)) else (if i.val < 245 then
      149 else (if i.val < 246 then 150 else 147))) else (if i.val < 250 then (if i.val < 248
      then 148 else (if i.val < 249 then 250 else 249)) else (if i.val < 252 then (if i.val <
      251 then 248 else 251) else (if i.val < 253 then 252 else 253)))))) else (if i.val < 279
      then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val < 255 then
      255 else (if i.val < 256 then 254 else 256)) else (if i.val < 258 then 257 else (if i.val
      < 259 then 258 else 259))) else (if i.val < 263 then (if i.val < 261 then 172 else (if
      i.val < 262 then 170 else 171)) else (if i.val < 264 then 173 else (if i.val < 265 then
      174 else 175)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then 177
      else (if i.val < 268 then 176 else 178)) else (if i.val < 270 then 179 else (if i.val <
      271 then 180 else 181))) else (if i.val < 275 then (if i.val < 273 then 275 else (if i.val
      < 274 then 273 else 274)) else (if i.val < 277 then (if i.val < 276 then 272 else 295)
      else (if i.val < 278 then 277 else 301))))) else (if i.val < 292 then (if i.val < 285 then
      (if i.val < 282 then (if i.val < 280 then 300 else (if i.val < 281 then 303 else 302))
      else (if i.val < 283 then 284 else (if i.val < 284 then 283 else 282))) else (if i.val <
      288 then (if i.val < 286 then 308 else (if i.val < 287 then 310 else 309)) else (if i.val
      < 290 then (if i.val < 289 then 288 else 290) else (if i.val < 291 then 289 else 316))))
      else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then 317 else (if i.val <
      294 then 315 else 318)) else (if i.val < 296 then 276 else (if i.val < 297 then 297 else
      296))) else (if i.val < 301 then (if i.val < 299 then 298 else (if i.val < 300 then 299
      else 279)) else (if i.val < 303 then (if i.val < 302 then 278 else 281) else (if i.val <
      304 then 280 else 306))))))) else (if i.val < 356 then (if i.val < 330 then (if i.val <
      317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 305 else (if i.val
      < 307 then 304 else 307)) else (if i.val < 309 then 285 else (if i.val < 310 then 287 else
      286))) else (if i.val < 314 then (if i.val < 312 then 313 else (if i.val < 313 then 312
      else 311)) else (if i.val < 315 then 314 else (if i.val < 316 then 293 else 291)))) else
      (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then 292 else (if i.val < 319
      then 294 else 322)) else (if i.val < 321 then 320 else (if i.val < 322 then 321 else
      319))) else (if i.val < 326 then (if i.val < 324 then 373 else (if i.val < 325 then 372
      else 371)) else (if i.val < 328 then (if i.val < 327 then 363 else 362) else (if i.val <
      329 then 361 else 332))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333
      then (if i.val < 331 then 330 else (if i.val < 332 then 331 else 329)) else (if i.val <
      334 then 376 else (if i.val < 335 then 374 else 375))) else (if i.val < 339 then (if i.val
      < 337 then 370 else (if i.val < 338 then 369 else 368)) else (if i.val < 341 then (if
      i.val < 340 then 367 else 353) else (if i.val < 342 then 352 else 351)))) else (if i.val <
      349 then (if i.val < 346 then (if i.val < 344 then 350 else (if i.val < 345 then 354 else
      356)) else (if i.val < 347 then 355 else (if i.val < 348 then 347 else 349))) else (if
      i.val < 352 then (if i.val < 350 then 348 else (if i.val < 351 then 343 else 342)) else
      (if i.val < 354 then (if i.val < 353 then 341 else 340) else (if i.val < 355 then 344 else
      346)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val <
      359 then (if i.val < 357 then 345 else (if i.val < 358 then 357 else 359)) else (if i.val
      < 360 then 358 else (if i.val < 361 then 360 else 328))) else (if i.val < 365 then (if
      i.val < 363 then 327 else (if i.val < 364 then 326 else 365)) else (if i.val < 366 then
      364 else (if i.val < 367 then 366 else 339)))) else (if i.val < 374 then (if i.val < 371
      then (if i.val < 369 then 338 else (if i.val < 370 then 337 else 336)) else (if i.val <
      372 then 325 else (if i.val < 373 then 324 else 323))) else (if i.val < 377 then (if i.val
      < 375 then 334 else (if i.val < 376 then 335 else 333)) else (if i.val < 379 then (if
      i.val < 378 then 406 else 407) else (if i.val < 380 then 404 else 405))))) else (if i.val
      < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 388 else (if
      i.val < 383 then 389 else 408)) else (if i.val < 385 then 412 else (if i.val < 386 then
      413 else 410))) else (if i.val < 390 then (if i.val < 388 then 411 else (if i.val < 389
      then 381 else 382)) else (if i.val < 392 then (if i.val < 391 then 414 else 393) else (if
      i.val < 393 then 394 else 391)))) else (if i.val < 400 then (if i.val < 397 then (if i.val
      < 395 then 392 else (if i.val < 396 then 395 else 396)) else (if i.val < 398 then 397 else
      (if i.val < 399 then 416 else 399))) else (if i.val < 403 then (if i.val < 401 then 400
      else (if i.val < 402 then 401 else 402)) else (if i.val < 405 then (if i.val < 404 then
      403 else 379) else (if i.val < 406 then 380 else 377))))))))) else (if i.val < 611 then
      (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
      i.val < 413 then (if i.val < 410 then (if i.val < 408 then 378 else (if i.val < 409 then
      383 else 409)) else (if i.val < 411 then 386 else (if i.val < 412 then 387 else 384)))
      else (if i.val < 416 then (if i.val < 414 then 385 else (if i.val < 415 then 390 else
      415)) else (if i.val < 417 then 398 else (if i.val < 418 then 460 else 463)))) else (if
      i.val < 425 then (if i.val < 422 then (if i.val < 420 then 464 else (if i.val < 421 then
      461 else 462)) else (if i.val < 423 then 465 else (if i.val < 424 then 466 else 468)))
      else (if i.val < 428 then (if i.val < 426 then 467 else (if i.val < 427 then 469 else
      473)) else (if i.val < 430 then (if i.val < 429 then 476 else 477) else (if i.val < 431
      then 474 else 475))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then
      (if i.val < 433 then 478 else (if i.val < 434 then 479 else 481)) else (if i.val < 436
      then 480 else (if i.val < 437 then 482 else 437))) else (if i.val < 441 then (if i.val <
      439 then 440 else (if i.val < 440 then 441 else 438)) else (if i.val < 443 then (if i.val
      < 442 then 439 else 442) else (if i.val < 444 then 443 else 445)))) else (if i.val < 451
      then (if i.val < 448 then (if i.val < 446 then 444 else (if i.val < 447 then 446 else
      486)) else (if i.val < 449 then 487 else (if i.val < 450 then 488 else 450))) else (if
      i.val < 454 then (if i.val < 452 then 451 else (if i.val < 453 then 452 else 453)) else
      (if i.val < 456 then (if i.val < 455 then 454 else 455) else (if i.val < 457 then 456 else
      457)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
      461 then (if i.val < 459 then 458 else (if i.val < 460 then 459 else 417)) else (if i.val
      < 462 then 420 else (if i.val < 463 then 421 else 418))) else (if i.val < 467 then (if
      i.val < 465 then 419 else (if i.val < 466 then 422 else 423)) else (if i.val < 468 then
      425 else (if i.val < 469 then 424 else 426)))) else (if i.val < 476 then (if i.val < 473
      then (if i.val < 471 then 470 else (if i.val < 472 then 471 else 472)) else (if i.val <
      474 then 427 else (if i.val < 475 then 430 else 431))) else (if i.val < 479 then (if i.val
      < 477 then 428 else (if i.val < 478 then 429 else 432)) else (if i.val < 481 then (if
      i.val < 480 then 433 else 435) else (if i.val < 482 then 434 else 436))))) else (if i.val
      < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 483 else (if
      i.val < 485 then 484 else 485)) else (if i.val < 487 then 447 else (if i.val < 488 then
      448 else 449))) else (if i.val < 492 then (if i.val < 490 then 494 else (if i.val < 491
      then 496 else 491)) else (if i.val < 494 then (if i.val < 493 then 498 else 493) else (if
      i.val < 495 then 489 else 495)))) else (if i.val < 502 then (if i.val < 499 then (if i.val
      < 497 then 490 else (if i.val < 498 then 497 else 492)) else (if i.val < 500 then 519 else
      (if i.val < 501 then 521 else 520))) else (if i.val < 505 then (if i.val < 503 then 522
      else (if i.val < 504 then 529 else 531)) else (if i.val < 507 then (if i.val < 506 then
      530 else 506) else (if i.val < 508 then 508 else 507))))))) else (if i.val < 560 then (if
      i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then (if i.val
      < 510 then 538 else (if i.val < 511 then 540 else 541)) else (if i.val < 513 then 539 else
      (if i.val < 514 then 542 else 543))) else (if i.val < 518 then (if i.val < 516 then 515
      else (if i.val < 517 then 516 else 517)) else (if i.val < 519 then 518 else (if i.val <
      520 then 499 else 501)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522
      then 500 else (if i.val < 523 then 502 else 523)) else (if i.val < 525 then 526 else (if
      i.val < 526 then 525 else 524))) else (if i.val < 530 then (if i.val < 528 then 527 else
      (if i.val < 529 then 528 else 503)) else (if i.val < 532 then (if i.val < 531 then 505
      else 504) else (if i.val < 533 then 532 else 535))))) else (if i.val < 547 then (if i.val
      < 540 then (if i.val < 537 then (if i.val < 535 then 534 else (if i.val < 536 then 533
      else 536)) else (if i.val < 538 then 537 else (if i.val < 539 then 509 else 512))) else
      (if i.val < 543 then (if i.val < 541 then 510 else (if i.val < 542 then 511 else 513))
      else (if i.val < 545 then (if i.val < 544 then 514 else 547) else (if i.val < 546 then 545
      else 546)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then 544 else
      (if i.val < 549 then 569 else 549)) else (if i.val < 551 then 575 else (if i.val < 552
      then 574 else 577))) else (if i.val < 556 then (if i.val < 554 then 576 else (if i.val <
      555 then 556 else 555)) else (if i.val < 558 then (if i.val < 557 then 554 else 583) else
      (if i.val < 559 then 582 else 585)))))) else (if i.val < 585 then (if i.val < 572 then (if
      i.val < 566 then (if i.val < 563 then (if i.val < 561 then 584 else (if i.val < 562 then
      561 else 562)) else (if i.val < 564 then 564 else (if i.val < 565 then 563 else 591)))
      else (if i.val < 569 then (if i.val < 567 then 592 else (if i.val < 568 then 590 else
      593)) else (if i.val < 570 then 548 else (if i.val < 571 then 571 else 570)))) else (if
      i.val < 578 then (if i.val < 575 then (if i.val < 573 then 572 else (if i.val < 574 then
      573 else 551)) else (if i.val < 576 then 550 else (if i.val < 577 then 553 else 552)))
      else (if i.val < 581 then (if i.val < 579 then 580 else (if i.val < 580 then 579 else
      578)) else (if i.val < 583 then (if i.val < 582 then 581 else 558) else (if i.val < 584
      then 557 else 560))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then
      (if i.val < 586 then 559 else (if i.val < 587 then 588 else 587)) else (if i.val < 589
      then 586 else (if i.val < 590 then 589 else 567))) else (if i.val < 594 then (if i.val <
      592 then 565 else (if i.val < 593 then 566 else 568)) else (if i.val < 596 then (if i.val
      < 595 then 597 else 595) else (if i.val < 597 then 596 else 594)))) else (if i.val < 604
      then (if i.val < 601 then (if i.val < 599 then 601 else (if i.val < 600 then 599 else
      600)) else (if i.val < 602 then 598 else (if i.val < 603 then 630 else 633))) else (if
      i.val < 607 then (if i.val < 605 then 631 else (if i.val < 606 then 632 else 606)) else
      (if i.val < 609 then (if i.val < 608 then 609 else 608) else (if i.val < 610 then 607 else
      639)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then (if i.val
      < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then 638 else (if
      i.val < 613 then 641 else 640)) else (if i.val < 615 then 614 else (if i.val < 616 then
      617 else 616))) else (if i.val < 620 then (if i.val < 618 then 615 else (if i.val < 619
      then 647 else 646)) else (if i.val < 621 then 649 else (if i.val < 622 then 648 else
      622)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then 623 else (if
      i.val < 625 then 625 else 624)) else (if i.val < 627 then 655 else (if i.val < 628 then
      656 else 654))) else (if i.val < 632 then (if i.val < 630 then 657 else (if i.val < 631
      then 602 else 604)) else (if i.val < 634 then (if i.val < 633 then 605 else 603) else (if
      i.val < 635 then 635 else 634))))) else (if i.val < 649 then (if i.val < 642 then (if
      i.val < 639 then (if i.val < 637 then 636 else (if i.val < 638 then 637 else 611)) else
      (if i.val < 640 then 610 else (if i.val < 641 then 613 else 612))) else (if i.val < 645
      then (if i.val < 643 then 644 else (if i.val < 644 then 643 else 642)) else (if i.val <
      647 then (if i.val < 646 then 645 else 619) else (if i.val < 648 then 618 else 621))))
      else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 620 else (if i.val <
      651 then 652 else 651)) else (if i.val < 653 then 650 else (if i.val < 654 then 653 else
      628))) else (if i.val < 658 then (if i.val < 656 then 626 else (if i.val < 657 then 627
      else 629)) else (if i.val < 660 then (if i.val < 659 then 661 else 659) else (if i.val <
      661 then 660 else 658)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
      then (if i.val < 665 then (if i.val < 663 then 746 else (if i.val < 664 then 745 else
      683)) else (if i.val < 666 then 747 else (if i.val < 667 then 748 else 751))) else (if
      i.val < 671 then (if i.val < 669 then 752 else (if i.val < 670 then 749 else 750)) else
      (if i.val < 672 then 753 else (if i.val < 673 then 754 else 755)))) else (if i.val < 680
      then (if i.val < 677 then (if i.val < 675 then 756 else (if i.val < 676 then 759 else
      760)) else (if i.val < 678 then 757 else (if i.val < 679 then 758 else 761))) else (if
      i.val < 683 then (if i.val < 681 then 762 else (if i.val < 682 then 772 else 771)) else
      (if i.val < 685 then (if i.val < 684 then 664 else 773) else (if i.val < 686 then 774 else
      777))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val <
      688 then 778 else (if i.val < 689 then 775 else 776)) else (if i.val < 691 then 779 else
      (if i.val < 692 then 780 else 781))) else (if i.val < 696 then (if i.val < 694 then 782
      else (if i.val < 695 then 785 else 786)) else (if i.val < 698 then (if i.val < 697 then
      783 else 784) else (if i.val < 699 then 787 else 788)))) else (if i.val < 706 then (if
      i.val < 703 then (if i.val < 701 then 701 else (if i.val < 702 then 700 else 702)) else
      (if i.val < 704 then 703 else (if i.val < 705 then 704 else 707))) else (if i.val < 709
      then (if i.val < 707 then 708 else (if i.val < 708 then 705 else 706)) else (if i.val <
      711 then (if i.val < 710 then 709 else 710) else (if i.val < 712 then 711 else 712)))))))
      else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then
      (if i.val < 716 then (if i.val < 714 then 715 else (if i.val < 715 then 716 else 713))
      else (if i.val < 717 then 714 else (if i.val < 718 then 717 else 718))) else (if i.val <
      722 then (if i.val < 720 then 797 else (if i.val < 721 then 798 else 799)) else (if i.val
      < 723 then 800 else (if i.val < 724 then 801 else 802)))) else (if i.val < 731 then (if
      i.val < 728 then (if i.val < 726 then 803 else (if i.val < 727 then 804 else 727)) else
      (if i.val < 729 then 728 else (if i.val < 730 then 729 else 730))) else (if i.val < 734
      then (if i.val < 732 then 731 else (if i.val < 733 then 732 else 733)) else (if i.val <
      736 then (if i.val < 735 then 734 else 735) else (if i.val < 737 then 736 else 737)))))
      else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then
      738 else (if i.val < 740 then 739 else 740)) else (if i.val < 742 then 741 else (if i.val
      < 743 then 742 else 743))) else (if i.val < 747 then (if i.val < 745 then 744 else (if
      i.val < 746 then 663 else 662)) else (if i.val < 749 then (if i.val < 748 then 665 else
      666) else (if i.val < 750 then 669 else 670)))) else (if i.val < 757 then (if i.val < 754
      then (if i.val < 752 then 667 else (if i.val < 753 then 668 else 671)) else (if i.val <
      755 then 672 else (if i.val < 756 then 673 else 674))) else (if i.val < 760 then (if i.val
      < 758 then 677 else (if i.val < 759 then 678 else 675)) else (if i.val < 762 then (if
      i.val < 761 then 676 else 679) else (if i.val < 763 then 680 else 763)))))) else (if i.val
      < 789 then (if i.val < 776 then (if i.val < 770 then (if i.val < 767 then (if i.val < 765
      then 764 else (if i.val < 766 then 765 else 766)) else (if i.val < 768 then 767 else (if
      i.val < 769 then 768 else 769))) else (if i.val < 773 then (if i.val < 771 then 770 else
      (if i.val < 772 then 682 else 681)) else (if i.val < 774 then 684 else (if i.val < 775
      then 685 else 688)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then
      689 else (if i.val < 778 then 686 else 687)) else (if i.val < 780 then 690 else (if i.val
      < 781 then 691 else 692))) else (if i.val < 785 then (if i.val < 783 then 693 else (if
      i.val < 784 then 696 else 697)) else (if i.val < 787 then (if i.val < 786 then 694 else
      695) else (if i.val < 788 then 698 else 699))))) else (if i.val < 802 then (if i.val < 795
      then (if i.val < 792 then (if i.val < 790 then 789 else (if i.val < 791 then 790 else
      791)) else (if i.val < 793 then 792 else (if i.val < 794 then 793 else 794))) else (if
      i.val < 798 then (if i.val < 796 then 795 else (if i.val < 797 then 796 else 719)) else
      (if i.val < 800 then (if i.val < 799 then 720 else 721) else (if i.val < 801 then 722 else
      723)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803 then 724 else (if
      i.val < 804 then 725 else 726)) else (if i.val < 806 then 810 else (if i.val < 807 then
      812 else 807))) else (if i.val < 811 then (if i.val < 809 then 814 else (if i.val < 810
      then 809 else 805)) else (if i.val < 813 then (if i.val < 812 then 811 else 806) else (if
      i.val < 814 then 813 else 808)))))))))))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed vertex, edge and branch bijections for this frame permutation. -/
def hint5 : Fin 815 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
    (if i.val < 25 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 37 then ⟨[0, 1], [0], [false]⟩
    else (if i.val < 43 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 46 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 48 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))))) else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53
    then (if i.val < 51 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 52 then ⟨[0,
    1, 2], [0, 1], [false, false]⟩ else ⟨[1, 0, 2], [1, 0], [false, false]⟩)) else (if i.val <
    54 then ⟨[1, 0, 2], [1, 0], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else
    (if i.val < 59 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 60 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else (if i.val < 61 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else
    ⟨[1, 0, 2], [1, 0], [false, false]⟩)))) else (if i.val < 68 then (if i.val < 65 then (if
    i.val < 63 then ⟨[1, 0, 2], [1, 0], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩) else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩)) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 152 then (if i.val <
    126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else (if i.val < 105 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val
    < 106 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩))) else (if i.val < 110 then (if i.val < 108 then ⟨[0, 1, 2, 3], [0, 1, 2], [false,
    false, false]⟩ else (if i.val < 109 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false, false]⟩
    else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else (if i.val < 111 then ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 112 then ⟨[1, 0, 2, 3], [1, 0, 2],
    [false, false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)))) else (if
    i.val < 119 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 122 then
    (if i.val < 120 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 121
    then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩)) else ⟨[0, 1, 2], [0, 1], [false, false]⟩))) else (if i.val < 139 then (if i.val <
    132 then (if i.val < 129 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 130 then
    ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 2, 1], [0, 1], [false, true]⟩)) else ⟨[0, 2,
    1], [0, 1], [false, true]⟩) else (if i.val < 145 then (if i.val < 142 then (if i.val < 140
    then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0,
    1, 2], [0, 1], [false, false]⟩) else (if i.val < 148 then (if i.val < 146 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else (if i.val < 147 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else
    ⟨[0, 2, 1], [0, 1], [false, true]⟩)) else ⟨[0, 2, 1], [0, 1], [false, true]⟩)))) else (if
    i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val < 155 then ⟨[0, 2, 1],
    [0, 1], [false, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else (if i.val < 161 then
    ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 162 then ⟨[0, 1, 2], [0, 1], [false,
    false]⟩ else ⟨[0, 2, 1], [0, 1], [false, true]⟩))) else (if i.val < 170 then ⟨[0, 2, 1], [0,
    1], [false, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else ⟨[0, 1, 2], [0, 1],
    [false, false]⟩))) else (if i.val < 305 then (if i.val < 254 then (if i.val < 228 then (if
    i.val < 215 then (if i.val < 209 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val <
    212 then (if i.val < 210 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 2, 1], [0, 1],
    [false, true]⟩) else ⟨[0, 2, 1], [0, 1], [false, true]⟩)) else (if i.val < 221 then (if
    i.val < 218 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else (if i.val < 219 then ⟨[0, 2, 1],
    [0, 1], [false, true]⟩ else (if i.val < 220 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else
    ⟨[0, 1, 2], [0, 1], [false, false]⟩))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if
    i.val < 241 then (if i.val < 234 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val <
    237 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 239 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else (if i.val < 240 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[0, 2,
    1], [0, 1], [false, true]⟩)))) else (if i.val < 247 then ⟨[0, 2, 1], [0, 1], [false, true]⟩
    else (if i.val < 250 then (if i.val < 248 then ⟨[0, 2, 1], [0, 1], [false, true]⟩ else ⟨[0,
    1, 2], [0, 1], [false, false]⟩) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)))) else ⟨[0, 1,
    2], [0, 1], [false, false]⟩) else (if i.val < 356 then (if i.val < 330 then (if i.val < 317
    then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 323 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩)) else (if i.val < 343 then ⟨[2, 1,
    0], [1, 0], [true, true]⟩ else (if i.val < 349 then (if i.val < 346 then (if i.val < 344
    then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0,
    1, 2], [0, 1], [false, false]⟩) else (if i.val < 352 then (if i.val < 350 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩) else (if i.val < 354 then
    ⟨[2, 1, 0], [1, 0], [true, true]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩))))) else (if
    i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val < 359 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else (if i.val < 360 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else
    (if i.val < 361 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[2, 1, 0], [1, 0], [true,
    true]⟩))) else (if i.val < 365 then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else (if i.val < 366
    then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else (if i.val < 367 then ⟨[0, 1, 2], [0, 1], [false,
    false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩)))) else (if i.val < 374 then ⟨[2, 1, 0], [1,
    0], [true, true]⟩ else (if i.val < 377 then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else ⟨[0, 1,
    2, 3], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 394 then (if i.val < 387 then
    (if i.val < 384 then (if i.val < 382 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false, false]⟩
    else (if i.val < 383 then ⟨[1, 0, 3, 2], [1, 0, 2], [false, false, true]⟩ else ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩) else (if i.val < 390 then (if i.val < 388 then ⟨[0, 1, 2, 3], [0, 1, 2], [false,
    false, false]⟩ else (if i.val < 389 then ⟨[1, 0, 2, 3], [1, 0, 2], [false, false, false]⟩
    else ⟨[1, 0, 3, 2], [1, 0, 2], [false, false, true]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩))))) else (if
    i.val < 611 then (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val <
    419 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 425 then ⟨[0, 1,
    2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 428 then (if i.val < 426 then ⟨[0,
    1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 427 then ⟨[0, 3, 2, 1], [0, 2,
    1], [false, true, true]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else ⟨[0,
    1, 2, 3], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 445 then (if i.val < 438
    then (if i.val < 435 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val <
    436 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 437 then ⟨[0, 3,
    2, 1], [0, 2, 1], [false, true, true]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩))) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 451 then
    (if i.val < 448 then (if i.val < 446 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩
    else (if i.val < 447 then ⟨[0, 3, 2, 1], [0, 2, 1], [false, true, true]⟩ else ⟨[0, 1, 2, 3],
    [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)
    else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 483 then (if i.val
    < 470 then (if i.val < 464 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if
    i.val < 467 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 468 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 469 then ⟨[0, 1, 2, 3],
    [0, 1, 2], [false, false, false]⟩ else ⟨[0, 3, 2, 1], [0, 2, 1], [false, true, true]⟩))))
    else (if i.val < 476 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val <
    479 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 481 then ⟨[0, 1,
    2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 482 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else ⟨[0, 3, 2, 1], [0, 2, 1], [false, true, true]⟩))))) else (if
    i.val < 496 then (if i.val < 489 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else
    ⟨[0, 1, 2], [0, 1], [false, false]⟩) else (if i.val < 502 then (if i.val < 499 then ⟨[0, 1,
    2], [0, 1], [false, false]⟩ else ⟨[0, 1], [0, 1], [false, false]⟩) else ⟨[0, 1], [0, 1],
    [false, false]⟩)))) else ⟨[0, 1], [0, 1], [false, false]⟩) else (if i.val < 713 then (if
    i.val < 662 then ⟨[0, 1], [0, 1], [false, false]⟩ else (if i.val < 687 then (if i.val < 674
    then (if i.val < 668 then (if i.val < 665 then (if i.val < 663 then ⟨[0, 1, 2], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 664 then ⟨[0, 1, 2], [0, 1, 2], [false, false,
    false]⟩ else ⟨[1, 0, 2], [0, 2, 1], [false, false, false]⟩)) else ⟨[0, 1, 2], [0, 1, 2],
    [false, false, false]⟩) else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩) else (if i.val <
    680 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 683 then ⟨[0, 1, 2],
    [0, 1, 2], [false, false, false]⟩ else (if i.val < 685 then (if i.val < 684 then ⟨[1, 0, 2],
    [0, 2, 1], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩) else
    ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩)))) else ⟨[0, 1, 2], [0, 1, 2], [false, false,
    false]⟩)) else (if i.val < 764 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if
    i.val < 789 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 802 then
    ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 808 then (if i.val < 805 then
    ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1], [0, 1, 2], [false, false,
    false]⟩) else ⟨[0, 1], [0, 1, 2], [false, false, false]⟩))))))))

/-- The kernel checks the supplied bijections without repeating permutation search. -/
theorem hints_valid5 : ∀ i, (hint5 i).check ((L24Graphs.graph i).relabel labels5)
    (L24Graphs.graph (destination5 i)) = true := by
  decide +kernel

/-- Every column is transported as a full decorated labelled graph. -/
theorem covered5 : ∀ i, ((L24Graphs.graph i).relabel labels5).isomorphic?
    (L24Graphs.graph (destination5 i)) = true := by
  intro i
  exact (hint5 i).check_sound _ _ (hints_valid5 i)

/-- The entire six-element group, retaining its inverse action on columns. -/
def labels : Fin 6 → Equiv.Perm (Fin 4) :=
  ![labels0, labels1, labels2, labels3, labels4, labels5]

/-- Verified column permutations corresponding to the marking permutations. -/
def destination : Fin 6 → Equiv.Perm (Fin 815) :=
  ![destination0, destination1, destination2, destination3, destination4, destination5]

/-- Exact equivariance of the finite graph frame under every retained label map. -/
theorem covered (p : Fin 6) : ∀ i, ((L24Graphs.graph i).relabel (labels p)).isomorphic?
    (L24Graphs.graph (destination p i)) = true := by
  fin_cases p
  · exact covered0
  · exact covered1
  · exact covered2
  · exact covered3
  · exact covered4
  · exact covered5

/-- Actual averaging of raw strata, including its factor one sixth. -/
noncomputable def average : StrataModule 2 (Fin 4) →ₗ[ℚ] StrataModule 2 (Fin 4) :=
  (1 / 6 : ℚ) • ∑ p : Fin 6, StrataModule.relabel (labels p)

/-- Efficient exact averaging: every output coefficient has six contributions. -/
def averageCoordinates (q : Coordinates 815) : Coordinates 815 :=
  (1 / 6 : ℚ) • ∑ p : Fin 6, fun i ↦ q ((destination p).symm i)

/-- Inverse coordinate reindexing represents the actual relabelled stratum sum. -/
theorem relabel_interpret (p : Fin 6) (q : Coordinates 815) :
    StrataModule.relabel (labels p) (interpret L24Graphs.columns q) =
      interpret L24Graphs.columns (fun i ↦ q ((destination p).symm i)) := by
  exact StrataOperation.relabel_interpret (labels p) L24Graphs.graph
    L24Graphs.graph_totalGenus q (destination p) (covered p)

/-- The rational average is tied to the full decorated graph operation. -/
theorem average_interpret (q : Coordinates 815) :
    average (interpret L24Graphs.columns q) =
      interpret L24Graphs.columns (averageCoordinates q) := by
  simp only [average, averageCoordinates, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, relabel_interpret]

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R}
attribute [local instance] strataRealizationModule

/-- The stable four-marked genus-two target. -/
theorem stableArity : StableArity 2 (Fin 4) := by norm_num [StableArity]

/-- Primitive label naturality preserves a realized zero under the sixfold average. -/
theorem average_vanishes (A : StrataRealization C 2 (Fin 4))
    (hl : ∀ p, A.RelabelCompatible A stableArity stableArity (labels p))
    (q : StrataModule 2 (Fin 4)) (hq : A.map q = 0) : A.map (average q) = 0 := by
  simp only [average, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hz (p : Fin 6) : A.map (StrataModule.relabel (labels p) q) = 0 := by
    rw [A.map_relabel A _ _ _ (hl p), hq, map_zero]
  simp only [hz, Finset.sum_const_zero, smul_zero]

end AxiomaticGW.L24Symmetry
