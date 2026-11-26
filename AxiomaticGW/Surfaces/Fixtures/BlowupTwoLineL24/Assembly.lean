/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineTable
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives00
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives01
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives02
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives03
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives04
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives05
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives06
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives07
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives08
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives09
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives10
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives11
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives12
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Representatives13
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports00
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports01
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports02
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports03
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports04
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports05
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports06
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports07
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports08
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports09
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports10
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports11
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports12
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transports13

/-! # The 815 original positions of the strict-transform line equation

Each lower-genus summand is certified by evaluation or by an equality of
decorated graph contractions. Every other position satisfies the original
zero-weight or higher-genus guard.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineH.Frame
set_option Elab.async false

private def atIndex (j : ℕ) : Prop :=
  ∀ h : j < 815, cachedWeighted ⟨j, h⟩ = candidate ⟨j, h⟩

private theorem checkedBlock0 (i : Fin 32) : atIndex (32 * 0 + i.val) := by
  fin_cases i <;> intro h
  · exact inactive 0 (by decide +kernel)
  · exact inactive 1 (by decide +kernel)
  · exact inactive 2 (by decide +kernel)
  · exact inactive 3 (by decide +kernel)
  · exact inactive 4 (by decide +kernel)
  · exact inactive 5 (by decide +kernel)
  · exact inactive 6 (by decide +kernel)
  · exact inactive 7 (by decide +kernel)
  · exact inactive 8 (by decide +kernel)
  · exact inactive 9 (by decide +kernel)
  · exact inactive 10 (by decide +kernel)
  · exact inactive 11 (by decide +kernel)
  · exact inactive 12 (by decide +kernel)
  · exact inactive 13 (by decide +kernel)
  · exact inactive 14 (by decide +kernel)
  · exact inactive 15 (by decide +kernel)
  · exact inactive 16 (by decide +kernel)
  · exact inactive 17 (by decide +kernel)
  · exact inactive 18 (by decide +kernel)
  · exact inactive 19 (by decide +kernel)
  · exact inactive 20 (by decide +kernel)
  · exact inactive 21 (by decide +kernel)
  · exact inactive 22 (by decide +kernel)
  · exact inactive 23 (by decide +kernel)
  · exact inactive 24 (by decide +kernel)
  · exact inactive 25 (by decide +kernel)
  · exact inactive 26 (by decide +kernel)
  · exact inactive 27 (by decide +kernel)
  · exact inactive 28 (by decide +kernel)
  · exact inactive 29 (by decide +kernel)
  · exact inactive 30 (by decide +kernel)
  · exact inactive 31 (by decide +kernel)

private theorem checkedBlock1 (i : Fin 32) : atIndex (32 * 1 + i.val) := by
  fin_cases i <;> intro h
  · exact inactive 32 (by decide +kernel)
  · exact inactive 33 (by decide +kernel)
  · exact inactive 34 (by decide +kernel)
  · exact inactive 35 (by decide +kernel)
  · exact inactive 36 (by decide +kernel)
  · exact inactive 37 (by decide +kernel)
  · exact inactive 38 (by decide +kernel)
  · exact inactive 39 (by decide +kernel)
  · exact inactive 40 (by decide +kernel)
  · exact inactive 41 (by decide +kernel)
  · exact inactive 42 (by decide +kernel)
  · exact inactive 43 (by decide +kernel)
  · exact inactive 44 (by decide +kernel)
  · exact inactive 45 (by decide +kernel)
  · exact inactive 46 (by decide +kernel)
  · exact inactive 47 (by decide +kernel)
  · exact inactive 48 (by decide +kernel)
  · exact inactive 49 (by decide +kernel)
  · exact inactive 50 (by decide +kernel)
  · exact inactive 51 (by decide +kernel)
  · exact inactive 52 (by decide +kernel)
  · exact inactive 53 (by decide +kernel)
  · exact inactive 54 (by decide +kernel)
  · exact inactive 55 (by decide +kernel)
  · exact inactive 56 (by decide +kernel)
  · exact inactive 57 (by decide +kernel)
  · exact inactive 58 (by decide +kernel)
  · exact inactive 59 (by decide +kernel)
  · exact inactive 60 (by decide +kernel)
  · exact inactive 61 (by decide +kernel)
  · exact inactive 62 (by decide +kernel)
  · exact inactive 63 (by decide +kernel)

private theorem checkedBlock2 (i : Fin 32) : atIndex (32 * 2 + i.val) := by
  fin_cases i <;> intro h
  · exact inactive 64 (by decide +kernel)
  · exact inactive 65 (by decide +kernel)
  · exact inactive 66 (by decide +kernel)
  · exact inactive 67 (by decide +kernel)
  · exact inactive 68 (by decide +kernel)
  · exact inactive 69 (by decide +kernel)
  · exact inactive 70 (by decide +kernel)
  · exact inactive 71 (by decide +kernel)
  · exact inactive 72 (by decide +kernel)
  · exact inactive 73 (by decide +kernel)
  · exact inactive 74 (by decide +kernel)
  · exact inactive 75 (by decide +kernel)
  · exact inactive 76 (by decide +kernel)
  · exact inactive 77 (by decide +kernel)
  · exact inactive 78 (by decide +kernel)
  · exact inactive 79 (by decide +kernel)
  · exact inactive 80 (by decide +kernel)
  · exact inactive 81 (by decide +kernel)
  · exact inactive 82 (by decide +kernel)
  · exact inactive 83 (by decide +kernel)
  · exact inactive 84 (by decide +kernel)
  · exact inactive 85 (by decide +kernel)
  · exact inactive 86 (by decide +kernel)
  · exact inactive 87 (by decide +kernel)
  · exact inactive 88 (by decide +kernel)
  · exact inactive 89 (by decide +kernel)
  · exact inactive 90 (by decide +kernel)
  · exact inactive 91 (by decide +kernel)
  · exact inactive 92 (by decide +kernel)
  · exact inactive 93 (by decide +kernel)
  · exact inactive 94 (by decide +kernel)
  · exact inactive 95 (by decide +kernel)

private theorem checkedBlock3 (i : Fin 32) : atIndex (32 * 3 + i.val) := by
  fin_cases i <;> intro h
  · exact inactive 96 (by decide +kernel)
  · exact inactive 97 (by decide +kernel)
  · exact inactive 98 (by decide +kernel)
  · exact inactive 99 (by decide +kernel)
  · exact inactive 100 (by decide +kernel)
  · exact inactive 101 (by decide +kernel)
  · exact inactive 102 (by decide +kernel)
  · exact inactive 103 (by decide +kernel)
  · exact inactive 104 (by decide +kernel)
  · exact inactive 105 (by decide +kernel)
  · exact inactive 106 (by decide +kernel)
  · exact inactive 107 (by decide +kernel)
  · exact inactive 108 (by decide +kernel)
  · exact inactive 109 (by decide +kernel)
  · exact inactive 110 (by decide +kernel)
  · exact inactive 111 (by decide +kernel)
  · exact inactive 112 (by decide +kernel)
  · exact inactive 113 (by decide +kernel)
  · exact inactive 114 (by decide +kernel)
  · exact inactive 115 (by decide +kernel)
  · exact inactive 116 (by decide +kernel)
  · exact inactive 117 (by decide +kernel)
  · exact inactive 118 (by decide +kernel)
  · exact inactive 119 (by decide +kernel)
  · exact inactive 120 (by decide +kernel)
  · exact checked121
  · exact checked122
  · exact checked123
  · exact checked124
  · exact checked125
  · exact checked126
  · exact checked127

private theorem checkedBlock4 (i : Fin 32) : atIndex (32 * 4 + i.val) := by
  fin_cases i <;> intro h
  · exact checked128
  · exact checked129
  · exact checked130
  · exact checked131
  · exact checked132
  · exact checked133
  · exact checked134
  · exact checked135
  · exact checked136
  · exact checked137
  · exact checked138
  · exact checked139
  · exact transfer 121 140 same140 checked121 (by decide +kernel)
  · exact transfer 122 141 same141 checked122 (by decide +kernel)
  · exact transfer 124 142 same142 checked124 (by decide +kernel)
  · exact transfer 126 143 same143 checked126 (by decide +kernel)
  · exact transfer 127 144 same144 checked127 (by decide +kernel)
  · exact transfer 128 145 same145 checked128 (by decide +kernel)
  · exact transfer 129 146 same146 checked129 (by decide +kernel)
  · exact transfer 130 147 same147 checked130 (by decide +kernel)
  · exact transfer 131 148 same148 checked131 (by decide +kernel)
  · exact transfer 132 149 same149 checked132 (by decide +kernel)
  · exact transfer 134 150 same150 checked134 (by decide +kernel)
  · exact transfer 135 151 same151 checked135 (by decide +kernel)
  · exact transfer 137 152 same152 checked137 (by decide +kernel)
  · exact transfer 138 153 same153 checked138 (by decide +kernel)
  · exact transfer 139 154 same154 checked139 (by decide +kernel)
  · exact transfer 121 155 same155 checked121 (by decide +kernel)
  · exact transfer 122 156 same156 checked122 (by decide +kernel)
  · exact transfer 124 157 same157 checked124 (by decide +kernel)
  · exact transfer 126 158 same158 checked126 (by decide +kernel)
  · exact transfer 127 159 same159 checked127 (by decide +kernel)

private theorem checkedBlock5 (i : Fin 32) : atIndex (32 * 5 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 128 160 same160 checked128 (by decide +kernel)
  · exact transfer 129 161 same161 checked129 (by decide +kernel)
  · exact transfer 130 162 same162 checked130 (by decide +kernel)
  · exact transfer 131 163 same163 checked131 (by decide +kernel)
  · exact transfer 132 164 same164 checked132 (by decide +kernel)
  · exact transfer 134 165 same165 checked134 (by decide +kernel)
  · exact transfer 135 166 same166 checked135 (by decide +kernel)
  · exact transfer 137 167 same167 checked137 (by decide +kernel)
  · exact transfer 138 168 same168 checked138 (by decide +kernel)
  · exact transfer 139 169 same169 checked139 (by decide +kernel)
  · exact checked170
  · exact checked171
  · exact checked172
  · exact checked173
  · exact checked174
  · exact checked175
  · exact checked176
  · exact checked177
  · exact checked178
  · exact checked179
  · exact checked180
  · exact checked181
  · exact checked182
  · exact checked183
  · exact checked184
  · exact checked185
  · exact checked186
  · exact checked187
  · exact checked188
  · exact checked189
  · exact checked190
  · exact checked191

private theorem checkedBlock6 (i : Fin 32) : atIndex (32 * 6 + i.val) := by
  fin_cases i <;> intro h
  · exact checked192
  · exact checked193
  · exact checked194
  · exact checked195
  · exact checked196
  · exact checked197
  · exact checked198
  · exact checked199
  · exact checked200
  · exact transfer 182 201 same201 checked182 (by decide +kernel)
  · exact transfer 183 202 same202 checked183 (by decide +kernel)
  · exact transfer 184 203 same203 checked184 (by decide +kernel)
  · exact transfer 185 204 same204 checked185 (by decide +kernel)
  · exact transfer 186 205 same205 checked186 (by decide +kernel)
  · exact transfer 187 206 same206 checked187 (by decide +kernel)
  · exact transfer 188 207 same207 checked188 (by decide +kernel)
  · exact transfer 189 208 same208 checked189 (by decide +kernel)
  · exact transfer 190 209 same209 checked190 (by decide +kernel)
  · exact transfer 191 210 same210 checked191 (by decide +kernel)
  · exact transfer 192 211 same211 checked192 (by decide +kernel)
  · exact transfer 193 212 same212 checked193 (by decide +kernel)
  · exact transfer 194 213 same213 checked194 (by decide +kernel)
  · exact transfer 195 214 same214 checked195 (by decide +kernel)
  · exact transfer 196 215 same215 checked196 (by decide +kernel)
  · exact transfer 197 216 same216 checked197 (by decide +kernel)
  · exact transfer 198 217 same217 checked198 (by decide +kernel)
  · exact transfer 199 218 same218 checked199 (by decide +kernel)
  · exact transfer 200 219 same219 checked200 (by decide +kernel)
  · exact checked220
  · exact checked221
  · exact checked222
  · exact checked223

private theorem checkedBlock7 (i : Fin 32) : atIndex (32 * 7 + i.val) := by
  fin_cases i <;> intro h
  · exact checked224
  · exact checked225
  · exact checked226
  · exact checked227
  · exact checked228
  · exact checked229
  · exact checked230
  · exact checked231
  · exact checked232
  · exact transfer 182 233 same233 checked182 (by decide +kernel)
  · exact transfer 183 234 same234 checked183 (by decide +kernel)
  · exact transfer 185 235 same235 checked185 (by decide +kernel)
  · exact transfer 187 236 same236 checked187 (by decide +kernel)
  · exact transfer 188 237 same237 checked188 (by decide +kernel)
  · exact transfer 189 238 same238 checked189 (by decide +kernel)
  · exact transfer 190 239 same239 checked190 (by decide +kernel)
  · exact transfer 191 240 same240 checked191 (by decide +kernel)
  · exact transfer 192 241 same241 checked192 (by decide +kernel)
  · exact transfer 193 242 same242 checked193 (by decide +kernel)
  · exact transfer 195 243 same243 checked195 (by decide +kernel)
  · exact transfer 196 244 same244 checked196 (by decide +kernel)
  · exact transfer 198 245 same245 checked198 (by decide +kernel)
  · exact transfer 199 246 same246 checked199 (by decide +kernel)
  · exact transfer 200 247 same247 checked200 (by decide +kernel)
  · exact transfer 220 248 same248 checked220 (by decide +kernel)
  · exact transfer 221 249 same249 checked221 (by decide +kernel)
  · exact transfer 222 250 same250 checked222 (by decide +kernel)
  · exact transfer 223 251 same251 checked223 (by decide +kernel)
  · exact transfer 224 252 same252 checked224 (by decide +kernel)
  · exact transfer 225 253 same253 checked225 (by decide +kernel)
  · exact transfer 226 254 same254 checked226 (by decide +kernel)
  · exact transfer 228 255 same255 checked228 (by decide +kernel)

private theorem checkedBlock8 (i : Fin 32) : atIndex (32 * 8 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 229 256 same256 checked229 (by decide +kernel)
  · exact transfer 230 257 same257 checked230 (by decide +kernel)
  · exact transfer 231 258 same258 checked231 (by decide +kernel)
  · exact transfer 232 259 same259 checked232 (by decide +kernel)
  · exact transfer 220 260 same260 checked220 (by decide +kernel)
  · exact transfer 221 261 same261 checked221 (by decide +kernel)
  · exact transfer 222 262 same262 checked222 (by decide +kernel)
  · exact transfer 223 263 same263 checked223 (by decide +kernel)
  · exact transfer 224 264 same264 checked224 (by decide +kernel)
  · exact transfer 225 265 same265 checked225 (by decide +kernel)
  · exact transfer 226 266 same266 checked226 (by decide +kernel)
  · exact transfer 228 267 same267 checked228 (by decide +kernel)
  · exact transfer 229 268 same268 checked229 (by decide +kernel)
  · exact transfer 230 269 same269 checked230 (by decide +kernel)
  · exact transfer 231 270 same270 checked231 (by decide +kernel)
  · exact transfer 232 271 same271 checked232 (by decide +kernel)
  · exact checked272
  · exact checked273
  · exact checked274
  · exact checked275
  · exact checked276
  · exact transfer 276 277 same277 checked276 (by decide +kernel)
  · exact checked278
  · exact checked279
  · exact checked280
  · exact checked281
  · exact checked282
  · exact transfer 276 283 same283 checked276 (by decide +kernel)
  · exact checked284
  · exact transfer 279 285 same285 checked279 (by decide +kernel)
  · exact transfer 280 286 same286 checked280 (by decide +kernel)
  · exact transfer 281 287 same287 checked281 (by decide +kernel)

private theorem checkedBlock9 (i : Fin 32) : atIndex (32 * 9 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 279 288 same288 checked279 (by decide +kernel)
  · exact transfer 280 289 same289 checked280 (by decide +kernel)
  · exact transfer 281 290 same290 checked281 (by decide +kernel)
  · exact checked291
  · exact checked292
  · exact checked293
  · exact checked294
  · exact checked295
  · exact checked296
  · exact checked297
  · exact checked298
  · exact checked299
  · exact transfer 296 300 same300 checked296 (by decide +kernel)
  · exact transfer 297 301 same301 checked297 (by decide +kernel)
  · exact transfer 298 302 same302 checked298 (by decide +kernel)
  · exact transfer 299 303 same303 checked299 (by decide +kernel)
  · exact checked304
  · exact checked305
  · exact checked306
  · exact checked307
  · exact transfer 296 308 same308 checked296 (by decide +kernel)
  · exact transfer 298 309 same309 checked298 (by decide +kernel)
  · exact transfer 299 310 same310 checked299 (by decide +kernel)
  · exact transfer 304 311 same311 checked304 (by decide +kernel)
  · exact transfer 305 312 same312 checked305 (by decide +kernel)
  · exact transfer 306 313 same313 checked306 (by decide +kernel)
  · exact transfer 307 314 same314 checked307 (by decide +kernel)
  · exact transfer 304 315 same315 checked304 (by decide +kernel)
  · exact transfer 305 316 same316 checked305 (by decide +kernel)
  · exact transfer 306 317 same317 checked306 (by decide +kernel)
  · exact transfer 307 318 same318 checked307 (by decide +kernel)
  · exact checked319

private theorem checkedBlock10 (i : Fin 32) : atIndex (32 * 10 + i.val) := by
  fin_cases i <;> intro h
  · exact checked320
  · exact checked321
  · exact checked322
  · exact checked323
  · exact checked324
  · exact checked325
  · exact transfer 323 326 same326 checked323 (by decide +kernel)
  · exact transfer 324 327 same327 checked324 (by decide +kernel)
  · exact transfer 325 328 same328 checked325 (by decide +kernel)
  · exact checked329
  · exact checked330
  · exact checked331
  · exact checked332
  · exact checked333
  · exact checked334
  · exact checked335
  · exact checked336
  · exact checked337
  · exact checked338
  · exact checked339
  · exact transfer 336 340 same340 checked336 (by decide +kernel)
  · exact transfer 337 341 same341 checked337 (by decide +kernel)
  · exact transfer 338 342 same342 checked338 (by decide +kernel)
  · exact transfer 339 343 same343 checked339 (by decide +kernel)
  · exact transfer 323 344 same344 checked323 (by decide +kernel)
  · exact transfer 324 345 same345 checked324 (by decide +kernel)
  · exact transfer 325 346 same346 checked325 (by decide +kernel)
  · exact transfer 323 347 same347 checked323 (by decide +kernel)
  · exact transfer 324 348 same348 checked324 (by decide +kernel)
  · exact transfer 325 349 same349 checked325 (by decide +kernel)
  · exact transfer 329 350 same350 checked329 (by decide +kernel)
  · exact transfer 330 351 same351 checked330 (by decide +kernel)

private theorem checkedBlock11 (i : Fin 32) : atIndex (32 * 11 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 331 352 same352 checked331 (by decide +kernel)
  · exact transfer 332 353 same353 checked332 (by decide +kernel)
  · exact transfer 333 354 same354 checked333 (by decide +kernel)
  · exact transfer 334 355 same355 checked334 (by decide +kernel)
  · exact transfer 335 356 same356 checked335 (by decide +kernel)
  · exact transfer 336 357 same357 checked336 (by decide +kernel)
  · exact transfer 337 358 same358 checked337 (by decide +kernel)
  · exact transfer 338 359 same359 checked338 (by decide +kernel)
  · exact transfer 339 360 same360 checked339 (by decide +kernel)
  · exact checked361
  · exact checked362
  · exact checked363
  · exact checked364
  · exact transfer 323 365 same365 checked323 (by decide +kernel)
  · exact transfer 323 366 same366 checked323 (by decide +kernel)
  · exact transfer 329 367 same367 checked329 (by decide +kernel)
  · exact transfer 330 368 same368 checked330 (by decide +kernel)
  · exact transfer 331 369 same369 checked331 (by decide +kernel)
  · exact transfer 332 370 same370 checked332 (by decide +kernel)
  · exact transfer 361 371 same371 checked361 (by decide +kernel)
  · exact transfer 362 372 same372 checked362 (by decide +kernel)
  · exact transfer 363 373 same373 checked363 (by decide +kernel)
  · exact transfer 361 374 same374 checked361 (by decide +kernel)
  · exact transfer 362 375 same375 checked362 (by decide +kernel)
  · exact transfer 363 376 same376 checked363 (by decide +kernel)
  · exact checked377
  · exact checked378
  · exact checked379
  · exact checked380
  · exact checked381
  · exact checked382
  · exact checked383

private theorem checkedBlock12 (i : Fin 32) : atIndex (32 * 12 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 377 384 same384 checked377 (by decide +kernel)
  · exact transfer 378 385 same385 checked378 (by decide +kernel)
  · exact transfer 379 386 same386 checked379 (by decide +kernel)
  · exact transfer 380 387 same387 checked380 (by decide +kernel)
  · exact transfer 381 388 same388 checked381 (by decide +kernel)
  · exact transfer 382 389 same389 checked382 (by decide +kernel)
  · exact transfer 383 390 same390 checked383 (by decide +kernel)
  · exact transfer 377 391 same391 checked377 (by decide +kernel)
  · exact transfer 378 392 same392 checked378 (by decide +kernel)
  · exact transfer 379 393 same393 checked379 (by decide +kernel)
  · exact transfer 380 394 same394 checked380 (by decide +kernel)
  · exact transfer 381 395 same395 checked381 (by decide +kernel)
  · exact transfer 382 396 same396 checked382 (by decide +kernel)
  · exact transfer 383 397 same397 checked383 (by decide +kernel)
  · exact checked398
  · exact checked399
  · exact checked400
  · exact transfer 399 401 same401 checked399 (by decide +kernel)
  · exact transfer 400 402 same402 checked400 (by decide +kernel)
  · exact checked403
  · exact transfer 399 404 same404 checked399 (by decide +kernel)
  · exact transfer 400 405 same405 checked400 (by decide +kernel)
  · exact transfer 399 406 same406 checked399 (by decide +kernel)
  · exact transfer 400 407 same407 checked400 (by decide +kernel)
  · exact transfer 403 408 same408 checked403 (by decide +kernel)
  · exact checked409
  · exact transfer 399 410 same410 checked399 (by decide +kernel)
  · exact transfer 400 411 same411 checked400 (by decide +kernel)
  · exact transfer 399 412 same412 checked399 (by decide +kernel)
  · exact transfer 400 413 same413 checked400 (by decide +kernel)
  · exact transfer 403 414 same414 checked403 (by decide +kernel)
  · exact transfer 409 415 same415 checked409 (by decide +kernel)

private theorem checkedBlock13 (i : Fin 32) : atIndex (32 * 13 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 409 416 same416 checked409 (by decide +kernel)
  · exact checked417
  · exact checked418
  · exact checked419
  · exact checked420
  · exact checked421
  · exact checked422
  · exact checked423
  · exact checked424
  · exact checked425
  · exact checked426
  · exact transfer 417 427 same427 checked417 (by decide +kernel)
  · exact transfer 418 428 same428 checked418 (by decide +kernel)
  · exact transfer 419 429 same429 checked419 (by decide +kernel)
  · exact transfer 420 430 same430 checked420 (by decide +kernel)
  · exact transfer 421 431 same431 checked421 (by decide +kernel)
  · exact transfer 422 432 same432 checked422 (by decide +kernel)
  · exact transfer 423 433 same433 checked423 (by decide +kernel)
  · exact transfer 424 434 same434 checked424 (by decide +kernel)
  · exact transfer 425 435 same435 checked425 (by decide +kernel)
  · exact transfer 426 436 same436 checked426 (by decide +kernel)
  · exact transfer 417 437 same437 checked417 (by decide +kernel)
  · exact transfer 418 438 same438 checked418 (by decide +kernel)
  · exact transfer 419 439 same439 checked419 (by decide +kernel)
  · exact transfer 420 440 same440 checked420 (by decide +kernel)
  · exact transfer 421 441 same441 checked421 (by decide +kernel)
  · exact transfer 422 442 same442 checked422 (by decide +kernel)
  · exact transfer 423 443 same443 checked423 (by decide +kernel)
  · exact transfer 424 444 same444 checked424 (by decide +kernel)
  · exact transfer 425 445 same445 checked425 (by decide +kernel)
  · exact transfer 426 446 same446 checked426 (by decide +kernel)
  · exact checked447

private theorem checkedBlock14 (i : Fin 32) : atIndex (32 * 14 + i.val) := by
  fin_cases i <;> intro h
  · exact checked448
  · exact checked449
  · exact checked450
  · exact checked451
  · exact checked452
  · exact transfer 451 453 same453 checked451 (by decide +kernel)
  · exact transfer 452 454 same454 checked452 (by decide +kernel)
  · exact checked455
  · exact checked456
  · exact checked457
  · exact transfer 457 458 same458 checked457 (by decide +kernel)
  · exact checked459
  · exact transfer 450 460 same460 checked450 (by decide +kernel)
  · exact transfer 451 461 same461 checked451 (by decide +kernel)
  · exact transfer 452 462 same462 checked452 (by decide +kernel)
  · exact transfer 451 463 same463 checked451 (by decide +kernel)
  · exact transfer 452 464 same464 checked452 (by decide +kernel)
  · exact transfer 455 465 same465 checked455 (by decide +kernel)
  · exact transfer 456 466 same466 checked456 (by decide +kernel)
  · exact transfer 457 467 same467 checked457 (by decide +kernel)
  · exact transfer 457 468 same468 checked457 (by decide +kernel)
  · exact transfer 459 469 same469 checked459 (by decide +kernel)
  · exact checked470
  · exact checked471
  · exact checked472
  · exact transfer 450 473 same473 checked450 (by decide +kernel)
  · exact transfer 451 474 same474 checked451 (by decide +kernel)
  · exact transfer 452 475 same475 checked452 (by decide +kernel)
  · exact transfer 451 476 same476 checked451 (by decide +kernel)
  · exact transfer 452 477 same477 checked452 (by decide +kernel)
  · exact transfer 455 478 same478 checked455 (by decide +kernel)
  · exact transfer 456 479 same479 checked456 (by decide +kernel)

private theorem checkedBlock15 (i : Fin 32) : atIndex (32 * 15 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 457 480 same480 checked457 (by decide +kernel)
  · exact transfer 457 481 same481 checked457 (by decide +kernel)
  · exact transfer 459 482 same482 checked459 (by decide +kernel)
  · exact transfer 470 483 same483 checked470 (by decide +kernel)
  · exact transfer 471 484 same484 checked471 (by decide +kernel)
  · exact transfer 472 485 same485 checked472 (by decide +kernel)
  · exact transfer 470 486 same486 checked470 (by decide +kernel)
  · exact transfer 471 487 same487 checked471 (by decide +kernel)
  · exact transfer 472 488 same488 checked472 (by decide +kernel)
  · exact checked489
  · exact transfer 489 490 same490 checked489 (by decide +kernel)
  · exact transfer 489 491 same491 checked489 (by decide +kernel)
  · exact checked492
  · exact checked493
  · exact transfer 493 494 same494 checked493 (by decide +kernel)
  · exact checked495
  · exact transfer 493 496 same496 checked493 (by decide +kernel)
  · exact transfer 495 497 same497 checked495 (by decide +kernel)
  · exact transfer 495 498 same498 checked495 (by decide +kernel)
  · exact checked499
  · exact checked500
  · exact checked501
  · exact checked502
  · exact transfer 499 503 same503 checked499 (by decide +kernel)
  · exact transfer 500 504 same504 checked500 (by decide +kernel)
  · exact transfer 501 505 same505 checked501 (by decide +kernel)
  · exact transfer 499 506 same506 checked499 (by decide +kernel)
  · exact transfer 500 507 same507 checked500 (by decide +kernel)
  · exact transfer 501 508 same508 checked501 (by decide +kernel)
  · exact checked509
  · exact checked510
  · exact checked511

private theorem checkedBlock16 (i : Fin 32) : atIndex (32 * 16 + i.val) := by
  fin_cases i <;> intro h
  · exact checked512
  · exact checked513
  · exact checked514
  · exact checked515
  · exact checked516
  · exact checked517
  · exact checked518
  · exact transfer 515 519 same519 checked515 (by decide +kernel)
  · exact transfer 516 520 same520 checked516 (by decide +kernel)
  · exact transfer 517 521 same521 checked517 (by decide +kernel)
  · exact transfer 518 522 same522 checked518 (by decide +kernel)
  · exact checked523
  · exact checked524
  · exact checked525
  · exact checked526
  · exact checked527
  · exact checked528
  · exact transfer 515 529 same529 checked515 (by decide +kernel)
  · exact transfer 516 530 same530 checked516 (by decide +kernel)
  · exact transfer 517 531 same531 checked517 (by decide +kernel)
  · exact transfer 523 532 same532 checked523 (by decide +kernel)
  · exact transfer 524 533 same533 checked524 (by decide +kernel)
  · exact transfer 525 534 same534 checked525 (by decide +kernel)
  · exact transfer 526 535 same535 checked526 (by decide +kernel)
  · exact transfer 527 536 same536 checked527 (by decide +kernel)
  · exact transfer 528 537 same537 checked528 (by decide +kernel)
  · exact transfer 523 538 same538 checked523 (by decide +kernel)
  · exact transfer 524 539 same539 checked524 (by decide +kernel)
  · exact transfer 525 540 same540 checked525 (by decide +kernel)
  · exact transfer 526 541 same541 checked526 (by decide +kernel)
  · exact transfer 527 542 same542 checked527 (by decide +kernel)
  · exact transfer 528 543 same543 checked528 (by decide +kernel)

private theorem checkedBlock17 (i : Fin 32) : atIndex (32 * 17 + i.val) := by
  fin_cases i <;> intro h
  · exact checked544
  · exact checked545
  · exact checked546
  · exact checked547
  · exact checked548
  · exact transfer 548 549 same549 checked548 (by decide +kernel)
  · exact checked550
  · exact checked551
  · exact checked552
  · exact checked553
  · exact checked554
  · exact transfer 548 555 same555 checked548 (by decide +kernel)
  · exact checked556
  · exact transfer 550 557 same557 checked550 (by decide +kernel)
  · exact transfer 551 558 same558 checked551 (by decide +kernel)
  · exact transfer 552 559 same559 checked552 (by decide +kernel)
  · exact transfer 553 560 same560 checked553 (by decide +kernel)
  · exact transfer 550 561 same561 checked550 (by decide +kernel)
  · exact transfer 551 562 same562 checked551 (by decide +kernel)
  · exact transfer 552 563 same563 checked552 (by decide +kernel)
  · exact transfer 553 564 same564 checked553 (by decide +kernel)
  · exact checked565
  · exact checked566
  · exact checked567
  · exact checked568
  · exact checked569
  · exact checked570
  · exact checked571
  · exact checked572
  · exact checked573
  · exact transfer 570 574 same574 checked570 (by decide +kernel)
  · exact transfer 571 575 same575 checked571 (by decide +kernel)

private theorem checkedBlock18 (i : Fin 32) : atIndex (32 * 18 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 572 576 same576 checked572 (by decide +kernel)
  · exact transfer 573 577 same577 checked573 (by decide +kernel)
  · exact checked578
  · exact checked579
  · exact checked580
  · exact checked581
  · exact transfer 570 582 same582 checked570 (by decide +kernel)
  · exact transfer 571 583 same583 checked571 (by decide +kernel)
  · exact transfer 572 584 same584 checked572 (by decide +kernel)
  · exact transfer 573 585 same585 checked573 (by decide +kernel)
  · exact transfer 578 586 same586 checked578 (by decide +kernel)
  · exact transfer 579 587 same587 checked579 (by decide +kernel)
  · exact transfer 580 588 same588 checked580 (by decide +kernel)
  · exact transfer 581 589 same589 checked581 (by decide +kernel)
  · exact transfer 578 590 same590 checked578 (by decide +kernel)
  · exact transfer 579 591 same591 checked579 (by decide +kernel)
  · exact transfer 580 592 same592 checked580 (by decide +kernel)
  · exact transfer 581 593 same593 checked581 (by decide +kernel)
  · exact checked594
  · exact checked595
  · exact checked596
  · exact checked597
  · exact checked598
  · exact checked599
  · exact checked600
  · exact checked601
  · exact checked602
  · exact checked603
  · exact checked604
  · exact checked605
  · exact transfer 602 606 same606 checked602 (by decide +kernel)
  · exact transfer 603 607 same607 checked603 (by decide +kernel)

private theorem checkedBlock19 (i : Fin 32) : atIndex (32 * 19 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 604 608 same608 checked604 (by decide +kernel)
  · exact transfer 605 609 same609 checked605 (by decide +kernel)
  · exact checked610
  · exact checked611
  · exact checked612
  · exact checked613
  · exact transfer 602 614 same614 checked602 (by decide +kernel)
  · exact transfer 603 615 same615 checked603 (by decide +kernel)
  · exact transfer 604 616 same616 checked604 (by decide +kernel)
  · exact transfer 605 617 same617 checked605 (by decide +kernel)
  · exact transfer 610 618 same618 checked610 (by decide +kernel)
  · exact transfer 611 619 same619 checked611 (by decide +kernel)
  · exact transfer 612 620 same620 checked612 (by decide +kernel)
  · exact transfer 613 621 same621 checked613 (by decide +kernel)
  · exact transfer 610 622 same622 checked610 (by decide +kernel)
  · exact transfer 611 623 same623 checked611 (by decide +kernel)
  · exact transfer 612 624 same624 checked612 (by decide +kernel)
  · exact transfer 613 625 same625 checked613 (by decide +kernel)
  · exact checked626
  · exact checked627
  · exact checked628
  · exact checked629
  · exact checked630
  · exact checked631
  · exact checked632
  · exact checked633
  · exact checked634
  · exact checked635
  · exact checked636
  · exact checked637
  · exact transfer 634 638 same638 checked634 (by decide +kernel)
  · exact transfer 635 639 same639 checked635 (by decide +kernel)

private theorem checkedBlock20 (i : Fin 32) : atIndex (32 * 20 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 636 640 same640 checked636 (by decide +kernel)
  · exact transfer 637 641 same641 checked637 (by decide +kernel)
  · exact checked642
  · exact checked643
  · exact checked644
  · exact checked645
  · exact transfer 634 646 same646 checked634 (by decide +kernel)
  · exact transfer 635 647 same647 checked635 (by decide +kernel)
  · exact transfer 636 648 same648 checked636 (by decide +kernel)
  · exact transfer 637 649 same649 checked637 (by decide +kernel)
  · exact transfer 642 650 same650 checked642 (by decide +kernel)
  · exact transfer 643 651 same651 checked643 (by decide +kernel)
  · exact transfer 644 652 same652 checked644 (by decide +kernel)
  · exact transfer 645 653 same653 checked645 (by decide +kernel)
  · exact transfer 642 654 same654 checked642 (by decide +kernel)
  · exact transfer 643 655 same655 checked643 (by decide +kernel)
  · exact transfer 644 656 same656 checked644 (by decide +kernel)
  · exact transfer 645 657 same657 checked645 (by decide +kernel)
  · exact checked658
  · exact checked659
  · exact checked660
  · exact checked661
  · exact checked662
  · exact checked663
  · exact checked664
  · exact checked665
  · exact checked666
  · exact checked667
  · exact checked668
  · exact checked669
  · exact checked670
  · exact checked671

private theorem checkedBlock21 (i : Fin 32) : atIndex (32 * 21 + i.val) := by
  fin_cases i <;> intro h
  · exact checked672
  · exact checked673
  · exact checked674
  · exact checked675
  · exact checked676
  · exact checked677
  · exact checked678
  · exact checked679
  · exact checked680
  · exact transfer 662 681 same681 checked662 (by decide +kernel)
  · exact transfer 663 682 same682 checked663 (by decide +kernel)
  · exact transfer 664 683 same683 checked664 (by decide +kernel)
  · exact transfer 665 684 same684 checked665 (by decide +kernel)
  · exact transfer 666 685 same685 checked666 (by decide +kernel)
  · exact transfer 667 686 same686 checked667 (by decide +kernel)
  · exact transfer 668 687 same687 checked668 (by decide +kernel)
  · exact transfer 669 688 same688 checked669 (by decide +kernel)
  · exact transfer 670 689 same689 checked670 (by decide +kernel)
  · exact transfer 671 690 same690 checked671 (by decide +kernel)
  · exact transfer 672 691 same691 checked672 (by decide +kernel)
  · exact transfer 673 692 same692 checked673 (by decide +kernel)
  · exact transfer 674 693 same693 checked674 (by decide +kernel)
  · exact transfer 675 694 same694 checked675 (by decide +kernel)
  · exact transfer 676 695 same695 checked676 (by decide +kernel)
  · exact transfer 677 696 same696 checked677 (by decide +kernel)
  · exact transfer 678 697 same697 checked678 (by decide +kernel)
  · exact transfer 679 698 same698 checked679 (by decide +kernel)
  · exact transfer 680 699 same699 checked680 (by decide +kernel)
  · exact transfer 662 700 same700 checked662 (by decide +kernel)
  · exact transfer 663 701 same701 checked663 (by decide +kernel)
  · exact transfer 664 702 same702 checked664 (by decide +kernel)
  · exact transfer 665 703 same703 checked665 (by decide +kernel)

private theorem checkedBlock22 (i : Fin 32) : atIndex (32 * 22 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 666 704 same704 checked666 (by decide +kernel)
  · exact transfer 667 705 same705 checked667 (by decide +kernel)
  · exact transfer 668 706 same706 checked668 (by decide +kernel)
  · exact transfer 669 707 same707 checked669 (by decide +kernel)
  · exact transfer 670 708 same708 checked670 (by decide +kernel)
  · exact transfer 671 709 same709 checked671 (by decide +kernel)
  · exact transfer 672 710 same710 checked672 (by decide +kernel)
  · exact transfer 673 711 same711 checked673 (by decide +kernel)
  · exact transfer 674 712 same712 checked674 (by decide +kernel)
  · exact transfer 675 713 same713 checked675 (by decide +kernel)
  · exact transfer 676 714 same714 checked676 (by decide +kernel)
  · exact transfer 677 715 same715 checked677 (by decide +kernel)
  · exact transfer 678 716 same716 checked678 (by decide +kernel)
  · exact transfer 679 717 same717 checked679 (by decide +kernel)
  · exact transfer 680 718 same718 checked680 (by decide +kernel)
  · exact checked719
  · exact checked720
  · exact checked721
  · exact checked722
  · exact checked723
  · exact checked724
  · exact checked725
  · exact checked726
  · exact checked727
  · exact transfer 727 728 same728 checked727 (by decide +kernel)
  · exact checked729
  · exact checked730
  · exact checked731
  · exact checked732
  · exact transfer 731 733 same733 checked731 (by decide +kernel)
  · exact transfer 732 734 same734 checked732 (by decide +kernel)
  · exact checked735

private theorem checkedBlock23 (i : Fin 32) : atIndex (32 * 23 + i.val) := by
  fin_cases i <;> intro h
  · exact checked736
  · exact checked737
  · exact checked738
  · exact checked739
  · exact checked740
  · exact transfer 739 741 same741 checked739 (by decide +kernel)
  · exact transfer 740 742 same742 checked740 (by decide +kernel)
  · exact checked743
  · exact checked744
  · exact transfer 727 745 same745 checked727 (by decide +kernel)
  · exact transfer 727 746 same746 checked727 (by decide +kernel)
  · exact transfer 729 747 same747 checked729 (by decide +kernel)
  · exact transfer 730 748 same748 checked730 (by decide +kernel)
  · exact transfer 731 749 same749 checked731 (by decide +kernel)
  · exact transfer 732 750 same750 checked732 (by decide +kernel)
  · exact transfer 731 751 same751 checked731 (by decide +kernel)
  · exact transfer 732 752 same752 checked732 (by decide +kernel)
  · exact transfer 735 753 same753 checked735 (by decide +kernel)
  · exact transfer 736 754 same754 checked736 (by decide +kernel)
  · exact transfer 737 755 same755 checked737 (by decide +kernel)
  · exact transfer 738 756 same756 checked738 (by decide +kernel)
  · exact transfer 739 757 same757 checked739 (by decide +kernel)
  · exact transfer 740 758 same758 checked740 (by decide +kernel)
  · exact transfer 739 759 same759 checked739 (by decide +kernel)
  · exact transfer 740 760 same760 checked740 (by decide +kernel)
  · exact transfer 743 761 same761 checked743 (by decide +kernel)
  · exact transfer 744 762 same762 checked744 (by decide +kernel)
  · exact checked763
  · exact checked764
  · exact checked765
  · exact checked766
  · exact checked767

private theorem checkedBlock24 (i : Fin 32) : atIndex (32 * 24 + i.val) := by
  fin_cases i <;> intro h
  · exact checked768
  · exact checked769
  · exact checked770
  · exact transfer 727 771 same771 checked727 (by decide +kernel)
  · exact transfer 727 772 same772 checked727 (by decide +kernel)
  · exact transfer 729 773 same773 checked729 (by decide +kernel)
  · exact transfer 730 774 same774 checked730 (by decide +kernel)
  · exact transfer 731 775 same775 checked731 (by decide +kernel)
  · exact transfer 732 776 same776 checked732 (by decide +kernel)
  · exact transfer 731 777 same777 checked731 (by decide +kernel)
  · exact transfer 732 778 same778 checked732 (by decide +kernel)
  · exact transfer 735 779 same779 checked735 (by decide +kernel)
  · exact transfer 736 780 same780 checked736 (by decide +kernel)
  · exact transfer 737 781 same781 checked737 (by decide +kernel)
  · exact transfer 738 782 same782 checked738 (by decide +kernel)
  · exact transfer 739 783 same783 checked739 (by decide +kernel)
  · exact transfer 740 784 same784 checked740 (by decide +kernel)
  · exact transfer 739 785 same785 checked739 (by decide +kernel)
  · exact transfer 740 786 same786 checked740 (by decide +kernel)
  · exact transfer 743 787 same787 checked743 (by decide +kernel)
  · exact transfer 744 788 same788 checked744 (by decide +kernel)
  · exact transfer 763 789 same789 checked763 (by decide +kernel)
  · exact transfer 764 790 same790 checked764 (by decide +kernel)
  · exact transfer 765 791 same791 checked765 (by decide +kernel)
  · exact transfer 766 792 same792 checked766 (by decide +kernel)
  · exact transfer 767 793 same793 checked767 (by decide +kernel)
  · exact transfer 768 794 same794 checked768 (by decide +kernel)
  · exact transfer 769 795 same795 checked769 (by decide +kernel)
  · exact transfer 770 796 same796 checked770 (by decide +kernel)
  · exact transfer 763 797 same797 checked763 (by decide +kernel)
  · exact transfer 764 798 same798 checked764 (by decide +kernel)
  · exact transfer 765 799 same799 checked765 (by decide +kernel)

private theorem checkedBlock25 (i : Fin 32) : atIndex (32 * 25 + i.val) := by
  fin_cases i <;> intro h
  · exact transfer 766 800 same800 checked766 (by decide +kernel)
  · exact transfer 767 801 same801 checked767 (by decide +kernel)
  · exact transfer 768 802 same802 checked768 (by decide +kernel)
  · exact transfer 769 803 same803 checked769 (by decide +kernel)
  · exact transfer 770 804 same804 checked770 (by decide +kernel)
  · exact checked805
  · exact transfer 805 806 same806 checked805 (by decide +kernel)
  · exact transfer 805 807 same807 checked805 (by decide +kernel)
  · exact checked808
  · exact checked809
  · exact transfer 809 810 same810 checked809 (by decide +kernel)
  · exact checked811
  · exact transfer 809 812 same812 checked809 (by decide +kernel)
  · exact transfer 811 813 same813 checked811 (by decide +kernel)
  · exact transfer 811 814 same814 checked811 (by decide +kernel)
  · exact False.elim ((by decide : ¬ 815 < 815) h)
  · exact False.elim ((by decide : ¬ 816 < 815) h)
  · exact False.elim ((by decide : ¬ 817 < 815) h)
  · exact False.elim ((by decide : ¬ 818 < 815) h)
  · exact False.elim ((by decide : ¬ 819 < 815) h)
  · exact False.elim ((by decide : ¬ 820 < 815) h)
  · exact False.elim ((by decide : ¬ 821 < 815) h)
  · exact False.elim ((by decide : ¬ 822 < 815) h)
  · exact False.elim ((by decide : ¬ 823 < 815) h)
  · exact False.elim ((by decide : ¬ 824 < 815) h)
  · exact False.elim ((by decide : ¬ 825 < 815) h)
  · exact False.elim ((by decide : ¬ 826 < 815) h)
  · exact False.elim ((by decide : ¬ 827 < 815) h)
  · exact False.elim ((by decide : ¬ 828 < 815) h)
  · exact False.elim ((by decide : ¬ 829 < 815) h)
  · exact False.elim ((by decide : ¬ 830 < 815) h)
  · exact False.elim ((by decide : ¬ 831 < 815) h)

/-- Numerically certified contraction at every position of the original expression. -/
theorem checked_all (j : Fin 815) : cachedWeighted j = candidate j := by
  have each (b : Fin 26) (t : Fin 32) : atIndex (32 * b.val + t.val) := by
    fin_cases b
    · exact checkedBlock0 t
    · exact checkedBlock1 t
    · exact checkedBlock2 t
    · exact checkedBlock3 t
    · exact checkedBlock4 t
    · exact checkedBlock5 t
    · exact checkedBlock6 t
    · exact checkedBlock7 t
    · exact checkedBlock8 t
    · exact checkedBlock9 t
    · exact checkedBlock10 t
    · exact checkedBlock11 t
    · exact checkedBlock12 t
    · exact checkedBlock13 t
    · exact checkedBlock14 t
    · exact checkedBlock15 t
    · exact checkedBlock16 t
    · exact checkedBlock17 t
    · exact checkedBlock18 t
    · exact checkedBlock19 t
    · exact checkedBlock20 t
    · exact checkedBlock21 t
    · exact checkedBlock22 t
    · exact checkedBlock23 t
    · exact checkedBlock24 t
    · exact checkedBlock25 t
  let b : Fin 26 := ⟨j.val / 32, by omega⟩
  let t : Fin 32 := ⟨j.val % 32, Nat.mod_lt _ (by decide)⟩
  have h : 32 * b.val + t.val = j.val := Nat.div_add_mod _ _
  have hx := each b t
  exact (h ▸ hx : atIndex j.val) j.isLt

end AxiomaticGW.BlowupTwoLineH.Frame

namespace AxiomaticGW.BlowupTwoLineH
open BlowupTwoLineBP

/-- The lower-genus constant in the shifted hyperplane equation for the strict line. -/
theorem constant_value :
    SurfaceGenusTwoBlowupScalar.constant 0 (line, .hyperplane) = 7 / 2880 := by
  rw [constant_eq_sum, ← Frame.sum_candidates]
  exact Finset.sum_congr rfl fun i _ ↦ (cachedWeighted_eq i).symm.trans (Frame.checked_all i)

/-- The genus-two invariant with a hyperplane descendant and a primary point. -/
theorem hyperplane_value : SurfaceGenusTwoBlowupRecursion.values 0 (line, .hyperplane) = 0 := by
  rw [value_eq_constant_sub, constant_value, sub_self]

end AxiomaticGW.BlowupTwoLineH

namespace AxiomaticGW.BlowupTwoLineTable
open SurfaceGenusTwoBlowupBoundedCertificate SurfaceGenusTwoBlowupOrder

/-- All five canonical families vanish at the strict transform of the line through both centers. -/
theorem strict_line_value (f : Family .blowupTwo) :
    SurfaceGenusTwoBlowupRecursion.values 0 (BlowupTwoLineBP.line, f) = 0 :=
  (BlowupTwoLineBP.family_eq_hyperplane f).trans BlowupTwoLineH.hyperplane_value

/-- The corrected original equations accept all twenty states through energy one. -/
theorem accepted : checkTable (X := .blowupTwo) 0 1 (candidate 0) = true :=
  zero_iff.mpr (BlowupTwoLineH.constant_eq_sum.symm.trans BlowupTwoLineH.constant_value)

/-- Read any of the twenty reconstructed values through energy one. -/
theorem values_eq (s : State .blowupTwo) (hs : SurfaceTarget.blowupTwo.effective.energy s.1 ≤ 1) :
    SurfaceGenusTwoBlowupRecursion.values 0 s = candidate 0 s :=
  (checkTable_sound 0 1 (candidate 0) accepted s hs).symm

end AxiomaticGW.BlowupTwoLineTable
