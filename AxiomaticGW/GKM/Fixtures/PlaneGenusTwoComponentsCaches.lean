/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsReplay

/-!
# Component selections for the original plane ancestor equations

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 6. -/
@[nolint defsWithUnderscore]
def indices_6 (j : Fin 17) : Fin 291 :=
  (#[
    2, 8, 9, 11, 16, 17, 18, 145,
    150, 155, 157, 158, 159, 163, 164, 166,
    167
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 6. -/
@[nolint defsWithUnderscore]
def cache_6 : ResidualCache .plane :=
  cacheFor indices_6 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 7. -/
@[nolint defsWithUnderscore]
def indices_7 (j : Fin 22) : Fin 291 :=
  (#[
    1, 7, 8, 9, 11, 16, 17, 18,
    19, 142, 143, 148, 154, 155, 156, 157,
    158, 159, 163, 166, 167, 168
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 7. -/
@[nolint defsWithUnderscore]
def cache_7 : ResidualCache .plane :=
  cacheFor indices_7 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 8. -/
@[nolint defsWithUnderscore]
def indices_8 (j : Fin 24) : Fin 291 :=
  (#[
    1, 7, 8, 9, 11, 16, 17, 18,
    19, 142, 143, 148, 154, 155, 156, 157,
    158, 159, 163, 164, 165, 166, 167, 168
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 8. -/
@[nolint defsWithUnderscore]
def cache_8 : ResidualCache .plane :=
  cacheFor indices_8 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 9. -/
@[nolint defsWithUnderscore]
def indices_9 (j : Fin 23) : Fin 291 :=
  (#[
    1, 7, 8, 9, 11, 16, 17, 18,
    19, 142, 148, 154, 155, 156, 157, 158,
    159, 163, 164, 165, 166, 167, 168
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 9. -/
@[nolint defsWithUnderscore]
def cache_9 : ResidualCache .plane :=
  cacheFor indices_9 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 10. -/
@[nolint defsWithUnderscore]
def indices_10 (j : Fin 24) : Fin 291 :=
  (#[
    11, 16, 43, 75, 84, 92, 121, 127,
    133, 138, 156, 158, 159, 166, 167, 168,
    213, 244, 264, 272, 277, 285, 289, 290
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 10. -/
@[nolint defsWithUnderscore]
def cache_10 : ResidualCache .plane :=
  cacheFor indices_10 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 11. -/
@[nolint defsWithUnderscore]
def indices_11 (j : Fin 24) : Fin 291 :=
  (#[
    11, 16, 43, 75, 84, 92, 121, 127,
    133, 138, 156, 158, 159, 166, 167, 168,
    213, 244, 264, 272, 277, 285, 289, 290
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 11. -/
@[nolint defsWithUnderscore]
def cache_11 : ResidualCache .plane :=
  cacheFor indices_11 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 12. -/
@[nolint defsWithUnderscore]
def indices_12 (j : Fin 21) : Fin 291 :=
  (#[
    11, 16, 44, 76, 85, 93, 122, 128,
    134, 158, 159, 166, 167, 214, 216, 245,
    265, 273, 278, 286, 290
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 12. -/
@[nolint defsWithUnderscore]
def cache_12 : ResidualCache .plane :=
  cacheFor indices_12 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 13. -/
@[nolint defsWithUnderscore]
def indices_13 (j : Fin 31) : Fin 291 :=
  (#[
    0, 3, 4, 5, 9, 11, 12, 13,
    14, 15, 16, 17, 139, 140, 146, 147,
    149, 150, 151, 152, 153, 156, 157, 158,
    159, 160, 163, 164, 166, 167, 168
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 13. -/
@[nolint defsWithUnderscore]
def cache_13 : ResidualCache .plane :=
  cacheFor indices_13 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 14. -/
@[nolint defsWithUnderscore]
def indices_14 (j : Fin 29) : Fin 291 :=
  (#[
    0, 3, 4, 5, 9, 11, 12, 13,
    14, 15, 16, 17, 139, 146, 147, 149,
    150, 156, 157, 158, 159, 160, 161, 162,
    163, 164, 166, 167, 168
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 14. -/
@[nolint defsWithUnderscore]
def cache_14 : ResidualCache .plane :=
  cacheFor indices_14 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 15. -/
@[nolint defsWithUnderscore]
def indices_15 (j : Fin 33) : Fin 291 :=
  (#[
    9, 11, 16, 17, 34, 67, 76, 85,
    93, 116, 122, 128, 134, 138, 145, 156,
    158, 159, 163, 166, 167, 168, 195, 197,
    233, 257, 260, 265, 273, 277, 278, 286,
    290
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 15. -/
@[nolint defsWithUnderscore]
def cache_15 : ResidualCache .plane :=
  cacheFor indices_15 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 16. -/
@[nolint defsWithUnderscore]
def indices_16 (j : Fin 32) : Fin 291 :=
  (#[
    10, 11, 16, 38, 71, 80, 89, 92,
    119, 125, 131, 133, 137, 138, 155, 156,
    157, 158, 159, 166, 167, 168, 205, 239,
    260, 270, 273, 283, 285, 286, 289, 290
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 16. -/
@[nolint defsWithUnderscore]
def cache_16 : ResidualCache .plane :=
  cacheFor indices_16 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 17. -/
@[nolint defsWithUnderscore]
def indices_17 (j : Fin 31) : Fin 291 :=
  (#[
    9, 11, 16, 17, 34, 67, 76, 85,
    93, 116, 122, 128, 134, 138, 145, 156,
    157, 158, 159, 163, 166, 167, 168, 197,
    205, 233, 260, 273, 277, 286, 290
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 17. -/
@[nolint defsWithUnderscore]
def cache_17 : ResidualCache .plane :=
  cacheFor indices_17 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 18. -/
@[nolint defsWithUnderscore]
def indices_18 (j : Fin 34) : Fin 291 :=
  (#[
    10, 11, 16, 38, 71, 80, 89, 92,
    119, 125, 131, 133, 137, 138, 155, 156,
    157, 158, 159, 166, 167, 168, 205, 207,
    239, 261, 270, 274, 283, 285, 286, 287,
    289, 290
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 18. -/
@[nolint defsWithUnderscore]
def cache_18 : ResidualCache .plane :=
  cacheFor indices_18 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 19. -/
@[nolint defsWithUnderscore]
def indices_19 (j : Fin 21) : Fin 291 :=
  (#[
    11, 16, 39, 72, 81, 90, 120, 126,
    132, 158, 159, 166, 167, 208, 211, 241,
    262, 271, 275, 284, 287
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 19. -/
@[nolint defsWithUnderscore]
def cache_19 : ResidualCache .plane :=
  cacheFor indices_19 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 20. -/
@[nolint defsWithUnderscore]
def indices_20 (j : Fin 31) : Fin 291 :=
  (#[
    9, 11, 16, 17, 22, 29, 35, 45,
    63, 68, 77, 86, 156, 157, 158, 159,
    166, 167, 168, 171, 174, 178, 187, 190,
    198, 206, 214, 217, 246, 265, 278
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 20. -/
@[nolint defsWithUnderscore]
def cache_20 : ResidualCache .plane :=
  cacheFor indices_20 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 21. -/
@[nolint defsWithUnderscore]
def indices_21 (j : Fin 41) : Fin 291 :=
  (#[
    5, 11, 12, 13, 16, 25, 48, 51,
    54, 85, 93, 99, 101, 103, 105, 106,
    128, 134, 145, 150, 156, 158, 159, 160,
    163, 164, 166, 167, 168, 178, 180, 220,
    226, 229, 234, 240, 245, 277, 278, 286,
    290
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 21. -/
@[nolint defsWithUnderscore]
def cache_21 : ResidualCache .plane :=
  cacheFor indices_21 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 22. -/
@[nolint defsWithUnderscore]
def indices_22 (j : Fin 30) : Fin 291 :=
  (#[
    9, 11, 16, 17, 22, 29, 35, 45,
    63, 68, 77, 86, 156, 157, 158, 159,
    163, 166, 167, 168, 174, 178, 190, 206,
    214, 226, 234, 246, 265, 278
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 22. -/
@[nolint defsWithUnderscore]
def cache_22 : ResidualCache .plane :=
  cacheFor indices_22 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 23. -/
@[nolint defsWithUnderscore]
def indices_23 (j : Fin 41) : Fin 291 :=
  (#[
    5, 11, 12, 13, 16, 25, 48, 51,
    54, 85, 93, 99, 101, 103, 105, 106,
    128, 134, 145, 150, 151, 156, 158, 159,
    160, 163, 164, 166, 167, 168, 180, 182,
    220, 229, 240, 245, 250, 253, 277, 286,
    290
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 23. -/
@[nolint defsWithUnderscore]
def cache_23 : ResidualCache .plane :=
  cacheFor indices_23 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 24. -/
@[nolint defsWithUnderscore]
def indices_24 (j : Fin 34) : Fin 291 :=
  (#[
    6, 11, 16, 26, 55, 56, 58, 92,
    107, 108, 110, 112, 133, 138, 151, 152,
    156, 158, 159, 166, 167, 168, 182, 212,
    221, 247, 248, 263, 266, 276, 279, 288,
    289, 290
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 24. -/
@[nolint defsWithUnderscore]
def cache_24 : ResidualCache .plane :=
  cacheFor indices_24 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 25. -/
@[nolint defsWithUnderscore]
def indices_25 (j : Fin 33) : Fin 291 :=
  (#[
    9, 11, 16, 17, 30, 64, 72, 81,
    90, 115, 120, 126, 132, 138, 144, 156,
    158, 159, 163, 166, 167, 168, 191, 194,
    230, 256, 259, 262, 271, 274, 275, 284,
    287
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 25. -/
@[nolint defsWithUnderscore]
def cache_25 : ResidualCache .plane :=
  cacheFor indices_25 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 26. -/
@[nolint defsWithUnderscore]
def indices_26 (j : Fin 33) : Fin 291 :=
  (#[
    10, 11, 16, 37, 70, 79, 88, 89,
    118, 124, 130, 131, 136, 137, 155, 156,
    157, 158, 159, 166, 167, 168, 201, 202,
    237, 259, 269, 271, 282, 283, 285, 286,
    287
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 26. -/
@[nolint defsWithUnderscore]
def cache_26 : ResidualCache .plane :=
  cacheFor indices_26 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 27. -/
@[nolint defsWithUnderscore]
def indices_27 (j : Fin 31) : Fin 291 :=
  (#[
    9, 11, 16, 17, 30, 64, 72, 81,
    90, 115, 120, 126, 132, 138, 144, 156,
    157, 158, 159, 163, 166, 167, 168, 191,
    202, 230, 259, 271, 274, 284, 287
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 27. -/
@[nolint defsWithUnderscore]
def cache_27 : ResidualCache .plane :=
  cacheFor indices_27 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 28. -/
@[nolint defsWithUnderscore]
def indices_28 (j : Fin 21) : Fin 291 :=
  (#[
    11, 16, 42, 74, 83, 91, 109, 111,
    113, 158, 159, 166, 167, 210, 215, 243,
    251, 254, 267, 280, 288
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 28. -/
@[nolint defsWithUnderscore]
def cache_28 : ResidualCache .plane :=
  cacheFor indices_28 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 29. -/
@[nolint defsWithUnderscore]
def indices_29 (j : Fin 31) : Fin 291 :=
  (#[
    9, 11, 16, 17, 21, 28, 32, 41,
    62, 65, 73, 82, 156, 157, 158, 159,
    166, 167, 168, 170, 173, 177, 186, 189,
    192, 203, 209, 211, 242, 262, 275
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 29. -/
@[nolint defsWithUnderscore]
def cache_29 : ResidualCache .plane :=
  cacheFor indices_29 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 30. -/
@[nolint defsWithUnderscore]
def indices_30 (j : Fin 41) : Fin 291 :=
  (#[
    5, 11, 12, 13, 16, 23, 46, 49,
    52, 81, 90, 98, 100, 102, 104, 106,
    126, 132, 144, 150, 156, 158, 159, 160,
    163, 164, 166, 167, 168, 175, 177, 218,
    225, 228, 231, 238, 241, 274, 275, 284,
    287
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 30. -/
@[nolint defsWithUnderscore]
def cache_30 : ResidualCache .plane :=
  cacheFor indices_30 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 31. -/
@[nolint defsWithUnderscore]
def indices_31 (j : Fin 30) : Fin 291 :=
  (#[
    9, 11, 16, 17, 21, 28, 32, 41,
    62, 65, 73, 82, 156, 157, 158, 159,
    163, 166, 167, 168, 173, 177, 189, 203,
    211, 225, 231, 242, 262, 275
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 31. -/
@[nolint defsWithUnderscore]
def cache_31 : ResidualCache .plane :=
  cacheFor indices_31 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 32. -/
@[nolint defsWithUnderscore]
def indices_32 (j : Fin 31) : Fin 291 :=
  (#[
    9, 11, 16, 17, 33, 66, 74, 83,
    91, 109, 111, 113, 114, 138, 141, 156,
    157, 158, 159, 163, 166, 167, 168, 196,
    204, 232, 258, 267, 276, 280, 288
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 32. -/
@[nolint defsWithUnderscore]
def cache_32 : ResidualCache .plane :=
  cacheFor indices_32 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 33. -/
@[nolint defsWithUnderscore]
def indices_33 (j : Fin 41) : Fin 291 :=
  (#[
    6, 10, 11, 16, 36, 55, 69, 78,
    87, 89, 107, 108, 117, 123, 129, 131,
    135, 137, 151, 152, 155, 156, 157, 158,
    159, 166, 167, 168, 199, 204, 235, 247,
    248, 258, 267, 268, 279, 281, 285, 286,
    288
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 33. -/
@[nolint defsWithUnderscore]
def cache_33 : ResidualCache .plane :=
  cacheFor indices_33 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 34. -/
@[nolint defsWithUnderscore]
def indices_34 (j : Fin 33) : Fin 291 :=
  (#[
    9, 11, 16, 17, 33, 66, 74, 83,
    91, 109, 111, 113, 114, 138, 141, 156,
    158, 159, 163, 166, 167, 168, 193, 196,
    232, 251, 254, 255, 258, 267, 276, 280,
    288
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 34. -/
@[nolint defsWithUnderscore]
def cache_34 : ResidualCache .plane :=
  cacheFor indices_34 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 35. -/
@[nolint defsWithUnderscore]
def indices_35 (j : Fin 31) : Fin 291 :=
  (#[
    9, 11, 16, 17, 20, 27, 31, 40,
    57, 59, 60, 61, 156, 157, 158, 159,
    166, 167, 168, 169, 172, 176, 183, 184,
    185, 188, 200, 210, 222, 251, 254
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 35. -/
@[nolint defsWithUnderscore]
def cache_35 : ResidualCache .plane :=
  cacheFor indices_35 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 36. -/
@[nolint defsWithUnderscore]
def indices_36 (j : Fin 41) : Fin 291 :=
  (#[
    5, 11, 12, 13, 16, 24, 47, 50,
    53, 83, 91, 94, 95, 96, 97, 106,
    109, 111, 141, 150, 156, 158, 159, 160,
    163, 164, 166, 167, 168, 176, 179, 219,
    223, 224, 227, 236, 243, 251, 276, 280,
    288
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 36. -/
@[nolint defsWithUnderscore]
def cache_36 : ResidualCache .plane :=
  cacheFor indices_36 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 37. -/
@[nolint defsWithUnderscore]
def indices_37 (j : Fin 30) : Fin 291 :=
  (#[
    9, 11, 16, 17, 20, 27, 31, 40,
    57, 59, 60, 61, 156, 157, 158, 159,
    163, 166, 167, 168, 172, 176, 188, 200,
    210, 222, 223, 224, 251, 254
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 37. -/
@[nolint defsWithUnderscore]
def cache_37 : ResidualCache .plane :=
  cacheFor indices_37 (by decide +kernel)

-- Numeric suffixes retain the stable external ancestor-row identifiers.
/-- Full component indices selected for ancestor row 38. -/
@[nolint defsWithUnderscore]
def indices_38 (j : Fin 41) : Fin 291 :=
  (#[
    5, 11, 12, 13, 16, 24, 47, 50,
    53, 83, 91, 94, 95, 96, 97, 106,
    109, 111, 141, 150, 151, 156, 158, 159,
    160, 163, 164, 166, 167, 168, 179, 181,
    219, 227, 236, 243, 249, 252, 276, 280,
    288
  ] : Array (Fin 291))[j.val]

/-- A proved partial component cache for ancestor row 38. -/
@[nolint defsWithUnderscore]
def cache_38 : ResidualCache .plane :=
  cacheFor indices_38 (by decide +kernel)

end AxiomaticGW.GKM.PlaneGenusTwoComponents
