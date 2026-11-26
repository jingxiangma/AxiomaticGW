/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroRawAssembly

/-!
# A checked relation between two fixed raw degree-two expressions

Witness SHA256: a68d166f6b3063ac4295b8104304e0644f2caca47d6f1a869a5d846fb591cef1
Decoded source SHA256: 423a3b07dc5bf612d824472708ad0cf79a5f445f5280a4ad0f649958770d83ed
All 28/16 actual occurrences and their rational coefficients are retained.
Finite decorated graph isomorphisms and rational linearity prove the equality.
This is not a geometric Mumford relation, a product-realization law, or a
Hodge/GW/CohFT identification. No new realization hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4000
set_option Elab.async false

namespace AxiomaticGW.GKM.HodgeDegreeTwoRawRelation

open AdmcyclesHodgeStrataCandidates
open EquivariantCoefficients
open scoped BigOperators

noncomputable section

attribute [local instance] strataRealizationModule

/-- The frame consists of the sixteen actual raw (0,2) source columns. -/
def representatives : Fin 16 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph6,
    rawGraph7,
    rawGraph8,
    rawGraph9,
    rawGraph10,
    rawGraph11,
    rawGraph12,
    rawGraph13,
    rawGraph14,
    rawGraph15,
    rawGraph16,
    rawGraph17,
    rawGraph18,
    rawGraph19,
    rawGraph20,
    rawGraph21]

/-- Exact coefficients of the actual (0,2) expression in this frame. -/
def collectedCoordinates : RelationCertificate.Coordinates 16 :=
  ![(-1 / 144),
    (-1 / 144),
    (-1 / 288),
    (-1 / 288),
    (-1 / 288),
    (-1 / 288),
    (1 / 1152),
    (1 / 144),
    (1 / 144),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288),
    (1 / 288)]

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint0 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso0 : rawGraph8 = representatives 2 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph8Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph8Exponents)
    (GraphIsomorphismHint.check_sound rawHint0 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint1 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso1 : rawGraph6 = representatives 0 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph6Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph6Exponents)
    (GraphIsomorphismHint.check_sound rawHint1 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint2 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso2 : rawGraph22 = rawGraph6 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph22Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph6Exponents)
    (GraphIsomorphismHint.check_sound rawHint2 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint3 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [true]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso3 : rawGraph23 = rawGraph9 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph23Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph9Exponents)
    (GraphIsomorphismHint.check_sound rawHint3 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint4 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso4 : rawGraph9 = representatives 3 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph9Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph9Exponents)
    (GraphIsomorphismHint.check_sound rawHint4 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint5 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso5 : rawGraph24 = rawGraph11 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph24Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph11Exponents)
    (GraphIsomorphismHint.check_sound rawHint5 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint6 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso6 : rawGraph25 = rawGraph10 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph25Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph10Exponents)
    (GraphIsomorphismHint.check_sound rawHint6 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint7 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso7 : rawGraph10 = representatives 4 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph10Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph10Exponents)
    (GraphIsomorphismHint.check_sound rawHint7 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint8 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso8 : rawGraph11 = representatives 5 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph11Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph11Exponents)
    (GraphIsomorphismHint.check_sound rawHint8 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint9 : GraphIsomorphismHint where
  vertices := [0]
  edges := []
  swaps := []

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso9 : rawGraph7 = representatives 1 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph7Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph7Exponents)
    (GraphIsomorphismHint.check_sound rawHint9 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint10 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso10 : rawGraph17 = representatives 11 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph17Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph17Exponents)
    (GraphIsomorphismHint.check_sound rawHint10 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint11 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso11 : rawGraph26 = rawGraph14 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph26Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph14Exponents)
    (GraphIsomorphismHint.check_sound rawHint11 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint12 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso12 : rawGraph27 = rawGraph13 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph27Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph13Exponents)
    (GraphIsomorphismHint.check_sound rawHint12 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint13 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso13 : rawGraph13 = representatives 7 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph13Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph13Exponents)
    (GraphIsomorphismHint.check_sound rawHint13 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint14 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso14 : rawGraph14 = representatives 8 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph14Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph14Exponents)
    (GraphIsomorphismHint.check_sound rawHint14 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint15 : GraphIsomorphismHint where
  vertices := [0]
  edges := []
  swaps := []

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso15 : rawGraph20 = representatives 14 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph20Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph20Exponents)
    (GraphIsomorphismHint.check_sound rawHint15 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint16 : GraphIsomorphismHint where
  vertices := [0]
  edges := []
  swaps := []

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso16 : rawGraph21 = representatives 15 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph21Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph21Exponents)
    (GraphIsomorphismHint.check_sound rawHint16 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint17 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso17 : rawGraph18 = representatives 12 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph18Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph18Exponents)
    (GraphIsomorphismHint.check_sound rawHint17 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint18 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0, 1]
  swaps := [false, true]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso18 : rawGraph28 = rawGraph15 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence9Candidate rawIncidence9Valid rawGraph28Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph15Exponents)
    (GraphIsomorphismHint.check_sound rawHint18 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint19 : GraphIsomorphismHint where
  vertices := [0, 2, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso19 : rawGraph29 = rawGraph16 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph29Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph16Exponents)
    (GraphIsomorphismHint.check_sound rawHint19 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint20 : GraphIsomorphismHint where
  vertices := [2, 0, 1]
  edges := [0, 1]
  swaps := [false, true]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso20 : rawGraph30 = rawGraph16 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence11Candidate rawIncidence11Valid rawGraph30Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph16Exponents)
    (GraphIsomorphismHint.check_sound rawHint20 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint21 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0, 1]
  swaps := [true, true]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso21 : rawGraph31 = rawGraph15 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph31Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph15Exponents)
    (GraphIsomorphismHint.check_sound rawHint21 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint22 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0, 1]
  swaps := [false, true]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso22 : rawGraph32 = rawGraph19 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph32Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph19Exponents)
    (GraphIsomorphismHint.check_sound rawHint22 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint23 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0, 1]
  swaps := [false, false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso23 : rawGraph12 = representatives 6 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph12Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph12Exponents)
    (GraphIsomorphismHint.check_sound rawHint23 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint24 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso24 : rawGraph33 = rawGraph18 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph33Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph18Exponents)
    (GraphIsomorphismHint.check_sound rawHint24 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint25 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso25 : rawGraph34 = rawGraph19 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence15Candidate rawIncidence15Valid rawGraph34Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph19Exponents)
    (GraphIsomorphismHint.check_sound rawHint25 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint26 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 0]
  swaps := [true, false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso26 : rawGraph35 = rawGraph19 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph35Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph19Exponents)
    (GraphIsomorphismHint.check_sound rawHint26 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint27 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 0]
  swaps := [true, false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso27 : rawGraph36 = rawGraph18 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph36Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph18Exponents)
    (GraphIsomorphismHint.check_sound rawHint27 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint28 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso28 : rawGraph15 = representatives 9 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph15Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph15Exponents)
    (GraphIsomorphismHint.check_sound rawHint28 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint29 : GraphIsomorphismHint where
  vertices := [0, 1, 2]
  edges := [0, 1]
  swaps := [false, false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso29 : rawGraph16 = representatives 10 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph16Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph16Exponents)
    (GraphIsomorphismHint.check_sound rawHint29 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed vertex, edge and ordered-branch bijections. -/
def rawHint30 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- Kernel-checked preservation of every source decoration. -/
theorem rawGraphIso30 : rawGraph19 = representatives 13 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph19Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph19Exponents)
    (GraphIsomorphismHint.check_sound rawHint30 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- One representative lookup for every original occurrence. -/
def index_1_1 : Fin 28 → Fin 16 :=
  ![2,
    0,
    0,
    3,
    3,
    5,
    4,
    4,
    5,
    1,
    11,
    8,
    7,
    7,
    8,
    14,
    15,
    12,
    9,
    10,
    10,
    9,
    13,
    6,
    12,
    13,
    13,
    12]

/-- Bind the full original column vector to checked source isomorphisms. -/
theorem columns_1_1_eq :
    ∀ i, raw11Degree2Columns i = representatives (index_1_1 i) := by
  intro i
  fin_cases i
  · exact rawGraphIso0
  · exact rawGraphIso1
  · exact rawGraphIso2
  · exact rawGraphIso3
  · exact rawGraphIso4
  · exact rawGraphIso5
  · exact rawGraphIso6
  · exact rawGraphIso7
  · exact rawGraphIso8
  · exact rawGraphIso9
  · exact rawGraphIso10
  · exact rawGraphIso11
  · exact rawGraphIso12
  · exact rawGraphIso13
  · exact rawGraphIso14
  · exact rawGraphIso15
  · exact rawGraphIso16
  · exact rawGraphIso17
  · exact rawGraphIso18
  · exact rawGraphIso19
  · exact rawGraphIso20
  · exact rawGraphIso21
  · exact rawGraphIso22
  · exact rawGraphIso23
  · exact rawGraphIso24
  · exact rawGraphIso25
  · exact rawGraphIso26
  · exact rawGraphIso27

/-- All actual source coefficients are collected, without dropping repetitions. -/
def grouped_1_1 : RelationCertificate.Coordinates 16 :=
  ∑ i, Pi.single (index_1_1 i) (raw11Degree2Coordinates i)

/-- Exact rational arithmetic in all sixteen coordinates. -/
theorem grouped_1_1_eq : grouped_1_1 = (2 : ℚ) • collectedCoordinates := by
  funext i
  fin_cases i <;> decide +kernel

/-- The previously decoded complete raw expression has these coordinates. -/
theorem raw_1_1_eq_collected : raw11Degree2 =
    RelationCertificate.interpret representatives ((2 : ℚ) • collectedCoordinates) := by
  calc
    raw11Degree2 = RelationCertificate.interpret representatives grouped_1_1 :=
      AdmcyclesHodgeStrataIsomorphisms.interpret_grouped
        _ _ _ _ columns_1_1_eq
    _ = _ := congrArg (RelationCertificate.interpret representatives)
      grouped_1_1_eq

/-- One representative lookup for every original occurrence. -/
def index_0_2 : Fin 16 → Fin 16 :=
  ![0,
    1,
    2,
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    11,
    12,
    13,
    14,
    15]

/-- Bind the full original column vector to checked source isomorphisms. -/
theorem columns_0_2_eq :
    ∀ i, raw02Degree2Columns i = representatives (index_0_2 i) := by
  intro i
  fin_cases i
  · exact rawGraphIso1
  · exact rawGraphIso9
  · exact rawGraphIso0
  · exact rawGraphIso4
  · exact rawGraphIso7
  · exact rawGraphIso8
  · exact rawGraphIso23
  · exact rawGraphIso13
  · exact rawGraphIso14
  · exact rawGraphIso28
  · exact rawGraphIso29
  · exact rawGraphIso10
  · exact rawGraphIso17
  · exact rawGraphIso30
  · exact rawGraphIso15
  · exact rawGraphIso16

/-- All actual source coefficients are collected, without dropping repetitions. -/
def grouped_0_2 : RelationCertificate.Coordinates 16 :=
  ∑ i, Pi.single (index_0_2 i) (raw02Degree2Coordinates i)

/-- Exact rational arithmetic in all sixteen coordinates. -/
theorem grouped_0_2_eq : grouped_0_2 = collectedCoordinates := by
  funext i
  fin_cases i <;> decide +kernel

/-- The previously decoded complete raw expression has these coordinates. -/
theorem raw_0_2_eq_collected : raw02Degree2 =
    RelationCertificate.interpret representatives (collectedCoordinates) := by
  calc
    raw02Degree2 = RelationCertificate.interpret representatives grouped_0_2 :=
      AdmcyclesHodgeStrataIsomorphisms.interpret_grouped
        _ _ _ _ columns_0_2_eq
    _ = _ := congrArg (RelationCertificate.interpret representatives)
      grouped_0_2_eq

/-- Equality of these two actual raw expressions, before any relation quotient. -/
theorem raw_degree_two_equal : raw11Degree2 = (2 : ℚ) • raw02Degree2 := by
  rw [raw_1_1_eq_collected, raw_0_2_eq_collected, map_smul]

/-- Rational linearity transfers the exact equality to the existing realization. -/
theorem map_raw_degree_two_equal {C : StableCurveCohomology Coefficient}
    (A : StrataRealization C 2 (Fin 1)) :
    A.map raw11Degree2 = (2 : Coefficient) • A.map raw02Degree2 := by
  rw [raw_degree_two_equal, two_smul, map_add, two_smul]

/-- The complete plane assembly needs only the original raw unit and (0,2) classes. -/
theorem plane_candidateClass_eq_raw_degree_two
    {C : StableCurveCohomology Coefficient} (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.Plane.candidateClass A =
      (x ^ 2 - x * y + y ^ 2) • A.map raw00Degree0 +
      (9 : Coefficient) • A.map raw02Degree2 := by
  rw [HodgeDegreeZeroRawAssembly.plane_candidateClass_eq_raw_regular,
    map_raw_degree_two_equal, smul_smul, add_assoc, ← add_smul]
  norm_num only

/-- The complete first blowup assembly has one actual degree-two raw expression. -/
theorem oneBlowup_candidateClass_eq_raw_degree_two
    {C : StableCurveCohomology Coefficient} (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.OneBlowup.candidateClass A =
      (8 : Coefficient) • A.map raw02Degree2 := by
  rw [HodgeDegreeZeroRawAssembly.oneBlowup_candidateClass_eq_raw_regular,
    map_raw_degree_two_equal, smul_smul]
  norm_num only

/-- The complete second blowup assembly preserves its signed raw unit term. -/
theorem twoBlowups_candidateClass_eq_raw_degree_two
    {C : StableCurveCohomology Coefficient} (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.candidateClass A =
      (-(x ^ 2 - x * y + y ^ 2)) • A.map raw00Degree0 +
      (7 : Coefficient) • A.map raw02Degree2 := by
  rw [HodgeDegreeZeroRawAssembly.twoBlowups_candidateClass_eq_raw_regular,
    map_raw_degree_two_equal, smul_smul, add_assoc, ← add_smul]
  norm_num only

end

end AxiomaticGW.GKM.HodgeDegreeTwoRawRelation
