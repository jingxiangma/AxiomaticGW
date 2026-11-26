/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Symmetry

/-!
# Auxiliary graph frame for the initial L24 comparison

The original 815 columns are unchanged. Forty-five further graph classes
retain the terms which cancel only after the prescribed marking average.
No auxiliary coefficient is dropped merely because it is absent from the
final candidate. All columns retain raw pushforward normalization.
-/

@[expose] public section

namespace AxiomaticGW.L24InitialGraphs
open RelationCertificate

set_option maxRecDepth 20000

/-- Upstream indices of the auxiliary graphs, retained for diagnostics. -/
def extraIndex : Fin 45 → ℕ :=
  ![59, 61, 70, 72, 86, 87, 89, 147, 149, 162, 165, 166, 184, 187, 188, 256, 257, 272, 273, 325,
    326, 713, 832, 852, 869, 871, 874, 876, 894, 903, 921, 922, 954, 1090, 1091, 1099, 1100,
    1106, 1107, 1494, 1496, 1499, 1501, 1542, 1543]

/-- Auxiliary column 0, with upstream index 59. -/
def extraGraph0 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Auxiliary column 1, with upstream index 61. -/
def extraGraph1 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Auxiliary column 2, with upstream index 70. -/
def extraGraph2 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Auxiliary column 3, with upstream index 72. -/
def extraGraph3 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 1]] }

/-- Auxiliary column 4, with upstream index 86. -/
def extraGraph4 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Auxiliary column 5, with upstream index 87. -/
def extraGraph5 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Auxiliary column 6, with upstream index 89. -/
def extraGraph6 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0]] }

/-- Auxiliary column 7, with upstream index 147. -/
def extraGraph7 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Auxiliary column 8, with upstream index 149. -/
def extraGraph8 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 1]] }

/-- Auxiliary column 9, with upstream index 162. -/
def extraGraph9 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Auxiliary column 10, with upstream index 165. -/
def extraGraph10 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Auxiliary column 11, with upstream index 166. -/
def extraGraph11 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 1],
    halfEdgePsiPower := ![![0, 0]] }

/-- Auxiliary column 12, with upstream index 184. -/
def extraGraph12 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0]] }

/-- Auxiliary column 13, with upstream index 187. -/
def extraGraph13 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Auxiliary column 14, with upstream index 188. -/
def extraGraph14 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 1],
    halfEdgePsiPower := ![![0, 0]] }

/-- Auxiliary column 15, with upstream index 256. -/
def extraGraph15 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 16, with upstream index 257. -/
def extraGraph16 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 17, with upstream index 272. -/
def extraGraph17 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 18, with upstream index 273. -/
def extraGraph18 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 19, with upstream index 325. -/
def extraGraph19 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 20, with upstream index 326. -/
def extraGraph20 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 21, with upstream index 713. -/
def extraGraph21 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 22, with upstream index 832. -/
def extraGraph22 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 23, with upstream index 852. -/
def extraGraph23 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 24, with upstream index 869. -/
def extraGraph24 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 25, with upstream index 871. -/
def extraGraph25 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 26, with upstream index 874. -/
def extraGraph26 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 27, with upstream index 876. -/
def extraGraph27 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 28, with upstream index 894. -/
def extraGraph28 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 29, with upstream index 903. -/
def extraGraph29 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 30, with upstream index 921. -/
def extraGraph30 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 31, with upstream index 922. -/
def extraGraph31 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 32, with upstream index 954. -/
def extraGraph32 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 33, with upstream index 1090. -/
def extraGraph33 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 34, with upstream index 1091. -/
def extraGraph34 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 35, with upstream index 1099. -/
def extraGraph35 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 36, with upstream index 1100. -/
def extraGraph36 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 37, with upstream index 1106. -/
def extraGraph37 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 38, with upstream index 1107. -/
def extraGraph38 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 39, with upstream index 1494. -/
def extraGraph39 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 40, with upstream index 1496. -/
def extraGraph40 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 41, with upstream index 1499. -/
def extraGraph41 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 42, with upstream index 1501. -/
def extraGraph42 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 43, with upstream index 1542. -/
def extraGraph43 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Auxiliary column 44, with upstream index 1543. -/
def extraGraph44 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Balanced lookup of all auxiliary decorated graphs. -/
def extraGraph : Fin 45 → DecoratedStableGraph (Fin 4) :=
  (fun i ↦ (if i.val < 22 then (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if
    i.val < 1 then extraGraph0 else extraGraph1) else (if i.val < 3 then extraGraph2 else (if
    i.val < 4 then extraGraph3 else extraGraph4))) else (if i.val < 8 then (if i.val < 6 then
    extraGraph5 else (if i.val < 7 then extraGraph6 else extraGraph7)) else (if i.val < 9 then
    extraGraph8 else (if i.val < 10 then extraGraph9 else extraGraph10)))) else (if i.val < 16
    then (if i.val < 13 then (if i.val < 12 then extraGraph11 else extraGraph12) else (if i.val
    < 14 then extraGraph13 else (if i.val < 15 then extraGraph14 else extraGraph15))) else (if
    i.val < 19 then (if i.val < 17 then extraGraph16 else (if i.val < 18 then extraGraph17 else
    extraGraph18)) else (if i.val < 20 then extraGraph19 else (if i.val < 21 then extraGraph20
    else extraGraph21))))) else (if i.val < 33 then (if i.val < 27 then (if i.val < 24 then (if
    i.val < 23 then extraGraph22 else extraGraph23) else (if i.val < 25 then extraGraph24 else
    (if i.val < 26 then extraGraph25 else extraGraph26))) else (if i.val < 30 then (if i.val <
    28 then extraGraph27 else (if i.val < 29 then extraGraph28 else extraGraph29)) else (if
    i.val < 31 then extraGraph30 else (if i.val < 32 then extraGraph31 else extraGraph32))))
    else (if i.val < 39 then (if i.val < 36 then (if i.val < 34 then extraGraph33 else (if i.val
    < 35 then extraGraph34 else extraGraph35)) else (if i.val < 37 then extraGraph36 else (if
    i.val < 38 then extraGraph37 else extraGraph38))) else (if i.val < 42 then (if i.val < 40
    then extraGraph39 else (if i.val < 41 then extraGraph40 else extraGraph41)) else (if i.val <
    43 then extraGraph42 else (if i.val < 44 then extraGraph43 else extraGraph44)))))))

/-- Each auxiliary column is a stable graph of the intended genus. -/
theorem extraGraph_totalGenus (i : Fin 45) : (extraGraph i).graph.totalGenus = 2 := by
  revert i
  decide +kernel

/-- The enlarged frame keeps the original columns first. -/
def graph : Fin 860 → DecoratedStableGraph (Fin 4) :=
  fun i ↦ Fin.addCases (m := 815) (n := 45) L24Graphs.graph extraGraph i

/-- The whole frame has genus two. -/
theorem graph_totalGenus (i : Fin 860) : (graph i).graph.totalGenus = 2 := by
  refine Fin.addCases (m := 815) (n := 45) (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa only [graph, Fin.addCases_left] using L24Graphs.graph_totalGenus j
  · simpa only [graph, Fin.addCases_right] using extraGraph_totalGenus j

/-- Quotient columns of the full temporary frame. -/
def columns (i : Fin 860) : TautologicalStratum 2 (Fin 4) :=
  .mk (graph i) (graph_totalGenus i)

/-- Extend a vector by zero on auxiliary columns, without identifying any classes. -/
def extend (q : Coordinates 815) : Coordinates 860 := fun i ↦ Fin.addCases (m := 815) (n := 45)
  q (fun _ ↦ 0) i

/-- Zero extension represents precisely the original free-strata expression. -/
theorem interpret_extend (q : Coordinates 815) :
    interpret columns (extend q) = interpret L24Graphs.columns q := by
  rw [interpret_apply, Fin.sum_univ_add (a := 815) (b := 45)]
  simp only [interpret_apply, extend, Fin.addCases_left,
    Fin.addCases_right, zero_smul, Finset.sum_const_zero, add_zero,
    columns, graph, L24Graphs.columns]

/-- The auxiliary column permutation for marking assignment 0. -/
def extraDestination0 : Equiv.Perm (Fin 45) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
    23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
    23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed full graph bijections for auxiliary marking assignment 0. -/
def extraHint0 : Fin 45 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 22 then (if i.val < 11 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 16
    then (if i.val < 13 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 14 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 15 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 33 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else (if i.val < 39 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else
    ⟨[0, 1], [0, 1], [false, false]⟩))))

/-- All incidences and decorations are checked for these auxiliary images. -/
theorem extraHints_valid0 : ∀ i, (extraHint0 i).check
    ((extraGraph i).relabel (L24Symmetry.labels 0))
    (extraGraph (extraDestination0 i)) = true := by
  decide +kernel

/-- The auxiliary column permutation for marking assignment 1. -/
def extraDestination1 : Equiv.Perm (Fin 45) where
  toFun := ![2, 3, 0, 1, 4, 6, 5, 8, 7, 12, 13, 14, 9, 10, 11, 17, 18, 15, 16, 20, 19, 21, 23,
    22, 26, 27, 24, 25, 29, 28, 31, 30, 32, 34, 33, 37, 38, 35, 36, 41, 42, 39, 40, 44, 43]
  invFun := ![2, 3, 0, 1, 4, 6, 5, 8, 7, 12, 13, 14, 9, 10, 11, 17, 18, 15, 16, 20, 19, 21, 23,
    22, 26, 27, 24, 25, 29, 28, 31, 30, 32, 34, 33, 37, 38, 35, 36, 41, 42, 39, 40, 44, 43]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed full graph bijections for auxiliary marking assignment 1. -/
def extraHint1 : Fin 45 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 22 then (if i.val < 11 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 16
    then (if i.val < 13 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 14 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 15 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 33 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else (if i.val < 39 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else
    ⟨[0, 1], [0, 1], [false, false]⟩))))

/-- All incidences and decorations are checked for these auxiliary images. -/
theorem extraHints_valid1 : ∀ i, (extraHint1 i).check
    ((extraGraph i).relabel (L24Symmetry.labels 1))
    (extraGraph (extraDestination1 i)) = true := by
  decide +kernel

/-- The auxiliary column permutation for marking assignment 2. -/
def extraDestination2 : Equiv.Perm (Fin 45) where
  toFun := ![1, 0, 7, 8, 10, 9, 11, 2, 3, 5, 4, 6, 14, 13, 12, 16, 15, 19, 20, 17, 18, 22, 21,
    23, 25, 24, 30, 31, 28, 32, 26, 27, 29, 37, 38, 36, 35, 33, 34, 40, 39, 43, 44, 41, 42]
  invFun := ![1, 0, 7, 8, 10, 9, 11, 2, 3, 5, 4, 6, 14, 13, 12, 16, 15, 19, 20, 17, 18, 22, 21,
    23, 25, 24, 30, 31, 28, 32, 26, 27, 29, 37, 38, 36, 35, 33, 34, 40, 39, 43, 44, 41, 42]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed full graph bijections for auxiliary marking assignment 2. -/
def extraHint2 : Fin 45 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 22 then (if i.val < 11 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 16
    then (if i.val < 13 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 14 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 15 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 33 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else (if i.val < 39 then (if i.val < 36 then (if i.val < 34 then
    ⟨[2, 1, 0], [1, 0], [true, true]⟩ else (if i.val < 35 then ⟨[2, 1, 0], [1, 0], [true, true]⟩
    else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 37 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩)) else ⟨[0, 1], [0, 1], [false,
    false]⟩))))

/-- All incidences and decorations are checked for these auxiliary images. -/
theorem extraHints_valid2 : ∀ i, (extraHint2 i).check
    ((extraGraph i).relabel (L24Symmetry.labels 2))
    (extraGraph (extraDestination2 i)) = true := by
  decide +kernel

/-- The auxiliary column permutation for marking assignment 3. -/
def extraDestination3 : Equiv.Perm (Fin 45) where
  toFun := ![3, 2, 8, 7, 13, 12, 14, 0, 1, 6, 4, 5, 11, 10, 9, 18, 17, 20, 19, 15, 16, 23, 21,
    22, 27, 26, 31, 30, 29, 32, 24, 25, 28, 35, 36, 38, 37, 34, 33, 42, 41, 44, 43, 39, 40]
  invFun := ![7, 8, 1, 0, 10, 11, 9, 3, 2, 14, 13, 12, 5, 4, 6, 19, 20, 16, 15, 18, 17, 22, 23,
    21, 30, 31, 25, 24, 32, 28, 27, 26, 29, 38, 37, 33, 34, 36, 35, 43, 44, 40, 39, 42, 41]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed full graph bijections for auxiliary marking assignment 3. -/
def extraHint3 : Fin 45 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 22 then (if i.val < 11 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 16
    then (if i.val < 13 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 14 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 15 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 33 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else (if i.val < 39 then (if i.val < 36 then (if i.val < 34 then
    ⟨[2, 1, 0], [1, 0], [true, true]⟩ else (if i.val < 35 then ⟨[2, 1, 0], [1, 0], [true, true]⟩
    else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 37 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[2, 1, 0], [1, 0], [true, true]⟩)) else ⟨[0, 1], [0, 1], [false,
    false]⟩))))

/-- All incidences and decorations are checked for these auxiliary images. -/
theorem extraHints_valid3 : ∀ i, (extraHint3 i).check
    ((extraGraph i).relabel (L24Symmetry.labels 3))
    (extraGraph (extraDestination3 i)) = true := by
  decide +kernel

/-- The auxiliary column permutation for marking assignment 4. -/
def extraDestination4 : Equiv.Perm (Fin 45) where
  toFun := ![7, 8, 1, 0, 10, 11, 9, 3, 2, 14, 13, 12, 5, 4, 6, 19, 20, 16, 15, 18, 17, 22, 23,
    21, 30, 31, 25, 24, 32, 28, 27, 26, 29, 38, 37, 33, 34, 36, 35, 43, 44, 40, 39, 42, 41]
  invFun := ![3, 2, 8, 7, 13, 12, 14, 0, 1, 6, 4, 5, 11, 10, 9, 18, 17, 20, 19, 15, 16, 23, 21,
    22, 27, 26, 31, 30, 29, 32, 24, 25, 28, 35, 36, 38, 37, 34, 33, 42, 41, 44, 43, 39, 40]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed full graph bijections for auxiliary marking assignment 4. -/
def extraHint4 : Fin 45 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 22 then (if i.val < 11 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 16
    then (if i.val < 13 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 14 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 15 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 33 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else (if i.val < 39 then (if i.val < 36 then ⟨[2, 1, 0], [1, 0],
    [true, true]⟩ else (if i.val < 37 then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else ⟨[0, 1, 2],
    [0, 1], [false, false]⟩)) else ⟨[0, 1], [0, 1], [false, false]⟩))))

/-- All incidences and decorations are checked for these auxiliary images. -/
theorem extraHints_valid4 : ∀ i, (extraHint4 i).check
    ((extraGraph i).relabel (L24Symmetry.labels 4))
    (extraGraph (extraDestination4 i)) = true := by
  decide +kernel

/-- The auxiliary column permutation for marking assignment 5. -/
def extraDestination5 : Equiv.Perm (Fin 45) where
  toFun := ![8, 7, 3, 2, 13, 14, 12, 1, 0, 11, 10, 9, 6, 4, 5, 20, 19, 18, 17, 16, 15, 23, 22,
    21, 31, 30, 27, 26, 32, 29, 25, 24, 28, 36, 35, 34, 33, 38, 37, 44, 43, 42, 41, 40, 39]
  invFun := ![8, 7, 3, 2, 13, 14, 12, 1, 0, 11, 10, 9, 6, 4, 5, 20, 19, 18, 17, 16, 15, 23, 22,
    21, 31, 30, 27, 26, 32, 29, 25, 24, 28, 36, 35, 34, 33, 38, 37, 44, 43, 42, 41, 40, 39]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Proposed full graph bijections for auxiliary marking assignment 5. -/
def extraHint5 : Fin 45 → GraphIsomorphismHint :=
  (fun i ↦ (if i.val < 22 then (if i.val < 11 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 16
    then (if i.val < 13 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 14 then ⟨[0, 1], [0],
    [false]⟩ else (if i.val < 15 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false,
    false]⟩))) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 33 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else (if i.val < 39 then (if i.val < 36 then ⟨[2, 1, 0], [1, 0],
    [true, true]⟩ else (if i.val < 37 then ⟨[2, 1, 0], [1, 0], [true, true]⟩ else ⟨[0, 1, 2],
    [0, 1], [false, false]⟩)) else ⟨[0, 1], [0, 1], [false, false]⟩))))

/-- All incidences and decorations are checked for these auxiliary images. -/
theorem extraHints_valid5 : ∀ i, (extraHint5 i).check
    ((extraGraph i).relabel (L24Symmetry.labels 5))
    (extraGraph (extraDestination5 i)) = true := by
  decide +kernel

/-- The six checked auxiliary permutations in the original averaging order. -/
def extraDestination : Fin 6 → Equiv.Perm (Fin 45) :=
  ![extraDestination0, extraDestination1, extraDestination2, extraDestination3,
    extraDestination4, extraDestination5]

/-- Auxiliary graph transport is an actual decorated graph isomorphism. -/
theorem extraCovered (p : Fin 6) (i : Fin 45) :
    ((extraGraph i).relabel (L24Symmetry.labels p)).isomorphic?
      (extraGraph (extraDestination p i)) = true := by
  fin_cases p
  · exact (extraHint0 i).check_sound _ _ (extraHints_valid0 i)
  · exact (extraHint1 i).check_sound _ _ (extraHints_valid1 i)
  · exact (extraHint2 i).check_sound _ _ (extraHints_valid2 i)
  · exact (extraHint3 i).check_sound _ _ (extraHints_valid3 i)
  · exact (extraHint4 i).check_sound _ _ (extraHints_valid4 i)
  · exact (extraHint5 i).check_sound _ _ (extraHints_valid5 i)

/-- Extend the old column permutations without mixing the two blocks. -/
def destination (p : Fin 6) : Equiv.Perm (Fin 860) :=
  (finSumFinEquiv.symm.trans
    ((L24Symmetry.destination p).sumCongr (extraDestination p))).trans finSumFinEquiv

/-- Every enlarged-frame column follows its actual marking transport. -/
theorem covered (p : Fin 6) (i : Fin 860) :
    ((graph i).relabel (L24Symmetry.labels p)).isomorphic?
      (graph (destination p i)) = true := by
  refine Fin.addCases (m := 815) (n := 45) (fun j ↦ ?_) (fun j ↦ ?_) i
  · change ((graph (j.castAdd 45)).relabel (L24Symmetry.labels p)).isomorphic?
      (graph (finSumFinEquiv (Sum.map (L24Symmetry.destination p) (extraDestination p)
        (finSumFinEquiv.symm (j.castAdd 45))))) = true
    rw [finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, finSumFinEquiv_apply_left]
    simpa only [graph, Fin.addCases_left] using L24Symmetry.covered p j
  · change ((graph (j.natAdd 815)).relabel (L24Symmetry.labels p)).isomorphic?
      (graph (finSumFinEquiv (Sum.map (L24Symmetry.destination p) (extraDestination p)
        (finSumFinEquiv.symm (j.natAdd 815))))) = true
    rw [finSumFinEquiv_symm_apply_natAdd, Sum.map_inr, finSumFinEquiv_apply_right]
    simpa only [graph, Fin.addCases_right] using extraCovered p j

/-- Exact averaging in the temporary frame retains every auxiliary coefficient. -/
def averageCoordinates (q : Coordinates 860) : Coordinates 860 :=
  (1 / 6 : ℚ) • ∑ p : Fin 6, fun i ↦ q ((destination p).symm i)

/-- The finite average denotes the existing raw graph average. -/
theorem average_interpret (q : Coordinates 860) :
    L24Symmetry.average (interpret columns q) = interpret columns (averageCoordinates q) := by
  have hr (p : Fin 6) := StrataOperation.relabel_interpret (L24Symmetry.labels p)
    graph graph_totalGenus q (destination p) (covered p)
  change ∀ p, StrataModule.relabel (L24Symmetry.labels p) (interpret columns q) =
    interpret columns (fun i ↦ q ((destination p).symm i)) at hr
  simp only [L24Symmetry.average, averageCoordinates, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum, hr]

end AxiomaticGW.L24InitialGraphs
