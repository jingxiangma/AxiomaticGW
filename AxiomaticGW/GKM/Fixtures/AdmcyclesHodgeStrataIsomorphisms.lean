/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataCandidates
public import AxiomaticGW.Tautological.GraphIsomorphismHint

/-!
# Exact isomorphism regrouping of two raw strata expressions

Witness SHA256: 04896b6d8492352593c7281ca2433bef43de2b9960cc14fe6e4700d4f1d3d0db
Decoded source SHA256: 423a3b07dc5bf612d824472708ad0cf79a5f445f5280a4ad0f649958770d83ed
The digests record provenance; the proofs reference the actual source definitions.
All 122/108 source occurrences and their exact coefficients are retained.
Only decorated graph isomorphisms and rational addition are used.
This proves equality in the free strata module. It does not identify Hodge
classes, certify a geometric product, or assert CohFT/GW compatibility.
-/

@[expose] public section

set_option maxRecDepth 4000
set_option Elab.async false

namespace AxiomaticGW.AdmcyclesHodgeStrataIsomorphisms

open scoped BigOperators
open AdmcyclesHodgeStrataCandidates

/-- Fixed representatives are selected actual raw source columns. -/
def representatives : Fin 44 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph42,
    rawGraph41,
    rawGraph83,
    rawGraph91,
    rawGraph93,
    rawGraph99,
    rawGraph118,
    rawGraph62,
    rawGraph64,
    rawGraph65,
    rawGraph51,
    rawGraph50,
    rawGraph63,
    rawGraph53,
    rawGraph54,
    rawGraph103,
    rawGraph100,
    rawGraph102,
    rawGraph109,
    rawGraph85,
    rawGraph101,
    rawGraph133,
    rawGraph113,
    rawGraph86,
    rawGraph89,
    rawGraph116,
    rawGraph137,
    rawGraph88,
    rawGraph87,
    rawGraph135,
    rawGraph47,
    rawGraph38,
    rawGraph49,
    rawGraph48,
    rawGraph57,
    rawGraph136,
    rawGraph46,
    rawGraph37,
    rawGraph80,
    rawGraph90,
    rawGraph67,
    rawGraph82,
    rawGraph40,
    rawGraph123]

/-- Exact collected coefficients in this fixed representative frame. -/
def collectedCoordinates : RelationCertificate.Coordinates 44 :=
  ![(-1 / 2304),
    (-1 / 4608),
    (1 / 2304),
    (1 / 3456),
    (1 / 2304),
    (1 / 1152),
    (1 / 1152),
    (-1 / 2304),
    (-1 / 2304),
    (-1 / 1152),
    (-1 / 1152),
    (-1 / 1152),
    (-1 / 2304),
    (-1 / 1152),
    (-1 / 1152),
    (1 / 576),
    (1 / 1152),
    (1 / 1152),
    (1 / 1152),
    (1 / 4608),
    (1 / 1152),
    (1 / 3456),
    (1 / 3456),
    (1 / 1152),
    (1 / 2304),
    (1 / 1728),
    (1 / 3456),
    (1 / 1152),
    (1 / 1152),
    (1 / 1152),
    (-1 / 1152),
    (-1 / 576),
    (-1 / 1152),
    (-1 / 1152),
    (-1 / 576),
    (1 / 1152),
    (-1 / 1152),
    (-1 / 1152),
    (1 / 576),
    (1 / 2304),
    (-1 / 3456),
    (1 / 1152),
    (-1 / 1152),
    (1 / 3456)]

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint0 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso0 : rawGraph37 = representatives 37 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph37Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph37Exponents)
    (GraphIsomorphismHint.check_sound rawHint0 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint1 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso1 : rawGraph38 = representatives 31 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph38Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph38Exponents)
    (GraphIsomorphismHint.check_sound rawHint1 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint2 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso2 : rawGraph39 = rawGraph38 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph39Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph38Exponents)
    (GraphIsomorphismHint.check_sound rawHint2 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint3 : GraphIsomorphismHint where
  vertices := [0]
  edges := []
  swaps := []

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso3 : rawGraph40 = representatives 42 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph40Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph40Exponents)
    (GraphIsomorphismHint.check_sound rawHint3 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint4 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso4 : rawGraph41 = representatives 1 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph41Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph41Exponents)
    (GraphIsomorphismHint.check_sound rawHint4 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint5 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso5 : rawGraph42 = representatives 0 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph42Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph42Exponents)
    (GraphIsomorphismHint.check_sound rawHint5 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint6 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0, 1]
  swaps := [false, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso6 : rawGraph43 = rawGraph42 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph43Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph42Exponents)
    (GraphIsomorphismHint.check_sound rawHint6 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint7 : GraphIsomorphismHint where
  vertices := [0]
  edges := [1, 0]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso7 : rawGraph44 = rawGraph42 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph44Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph42Exponents)
    (GraphIsomorphismHint.check_sound rawHint7 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint8 : GraphIsomorphismHint where
  vertices := [0]
  edges := [1, 0]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso8 : rawGraph45 = rawGraph42 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph45Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph42Exponents)
    (GraphIsomorphismHint.check_sound rawHint8 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint9 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso9 : rawGraph46 = representatives 36 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph46Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph46Exponents)
    (GraphIsomorphismHint.check_sound rawHint9 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint10 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso10 : rawGraph47 = representatives 30 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph47Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph47Exponents)
    (GraphIsomorphismHint.check_sound rawHint10 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint11 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso11 : rawGraph48 = representatives 33 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph48Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph48Exponents)
    (GraphIsomorphismHint.check_sound rawHint11 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint12 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso12 : rawGraph49 = representatives 32 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph49Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph49Exponents)
    (GraphIsomorphismHint.check_sound rawHint12 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint13 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso13 : rawGraph50 = representatives 11 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph50Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph50Exponents)
    (GraphIsomorphismHint.check_sound rawHint13 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint14 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso14 : rawGraph51 = representatives 10 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph51Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph51Exponents)
    (GraphIsomorphismHint.check_sound rawHint14 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint15 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0]
  swaps := [true, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso15 : rawGraph52 = rawGraph51 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph52Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph51Exponents)
    (GraphIsomorphismHint.check_sound rawHint15 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint16 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso16 : rawGraph53 = representatives 13 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph53Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph53Exponents)
    (GraphIsomorphismHint.check_sound rawHint16 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint17 : GraphIsomorphismHint where
  vertices := [0, 1, 2]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso17 : rawGraph54 = representatives 14 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph54Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph54Exponents)
    (GraphIsomorphismHint.check_sound rawHint17 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint18 : GraphIsomorphismHint where
  vertices := [1, 0, 2]
  edges := [1, 0]
  swaps := [true, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso18 : rawGraph55 = rawGraph54 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph55Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph54Exponents)
    (GraphIsomorphismHint.check_sound rawHint18 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint19 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso19 : rawGraph56 = rawGraph46 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph56Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph46Exponents)
    (GraphIsomorphismHint.check_sound rawHint19 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint20 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso20 : rawGraph57 = representatives 34 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph57Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph57Exponents)
    (GraphIsomorphismHint.check_sound rawHint20 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint21 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso21 : rawGraph58 = rawGraph49 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph58Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph49Exponents)
    (GraphIsomorphismHint.check_sound rawHint21 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint22 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso22 : rawGraph59 = rawGraph48 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph59Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph48Exponents)
    (GraphIsomorphismHint.check_sound rawHint22 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint23 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso23 : rawGraph60 = rawGraph47 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph60Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph47Exponents)
    (GraphIsomorphismHint.check_sound rawHint23 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint24 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0, 1]
  swaps := [false, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso24 : rawGraph61 = rawGraph53 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph61Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph53Exponents)
    (GraphIsomorphismHint.check_sound rawHint24 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint25 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso25 : rawGraph62 = representatives 7 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph62Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph62Exponents)
    (GraphIsomorphismHint.check_sound rawHint25 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint26 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso26 : rawGraph63 = representatives 12 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph63Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph63Exponents)
    (GraphIsomorphismHint.check_sound rawHint26 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint27 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso27 : rawGraph64 = representatives 8 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph64Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph64Exponents)
    (GraphIsomorphismHint.check_sound rawHint27 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint28 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso28 : rawGraph65 = representatives 9 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph65Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph65Exponents)
    (GraphIsomorphismHint.check_sound rawHint28 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint29 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso29 : rawGraph66 = rawGraph65 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph66Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph65Exponents)
    (GraphIsomorphismHint.check_sound rawHint29 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint30 : GraphIsomorphismHint where
  vertices := [0]
  edges := []
  swaps := []

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso30 : rawGraph67 = representatives 40 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph67Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph67Exponents)
    (GraphIsomorphismHint.check_sound rawHint30 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint31 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso31 : rawGraph68 = rawGraph50 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph68Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph50Exponents)
    (GraphIsomorphismHint.check_sound rawHint31 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint32 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 0]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso32 : rawGraph69 = rawGraph53 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence15Candidate rawIncidence15Valid rawGraph69Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph53Exponents)
    (GraphIsomorphismHint.check_sound rawHint32 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint33 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso33 : rawGraph70 = rawGraph65 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph70Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph65Exponents)
    (GraphIsomorphismHint.check_sound rawHint33 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint34 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0, 1]
  swaps := [false, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso34 : rawGraph71 = rawGraph51 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence9Candidate rawIncidence9Valid rawGraph71Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph51Exponents)
    (GraphIsomorphismHint.check_sound rawHint34 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint35 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso35 : rawGraph72 = rawGraph53 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph72Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph53Exponents)
    (GraphIsomorphismHint.check_sound rawHint35 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint36 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 0]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso36 : rawGraph73 = rawGraph50 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph73Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph50Exponents)
    (GraphIsomorphismHint.check_sound rawHint36 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint37 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 0]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso37 : rawGraph74 = rawGraph65 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph74Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph65Exponents)
    (GraphIsomorphismHint.check_sound rawHint37 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint38 : GraphIsomorphismHint where
  vertices := [1, 2, 0]
  edges := [0, 1]
  swaps := [true, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso38 : rawGraph75 = rawGraph54 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph75Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph54Exponents)
    (GraphIsomorphismHint.check_sound rawHint38 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint39 : GraphIsomorphismHint where
  vertices := [2, 0, 1]
  edges := [0, 1]
  swaps := [false, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso39 : rawGraph76 = rawGraph54 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence11Candidate rawIncidence11Valid rawGraph76Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph54Exponents)
    (GraphIsomorphismHint.check_sound rawHint39 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint40 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0, 1]
  swaps := [true, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso40 : rawGraph77 = rawGraph51 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph77Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph51Exponents)
    (GraphIsomorphismHint.check_sound rawHint40 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint41 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0, 1]
  swaps := [false, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso41 : rawGraph78 = rawGraph63 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph78Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph63Exponents)
    (GraphIsomorphismHint.check_sound rawHint41 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint42 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso42 : rawGraph79 = rawGraph57 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph79Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph57Exponents)
    (GraphIsomorphismHint.check_sound rawHint42 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint43 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso43 : rawGraph80 = representatives 38 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph80Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph80Exponents)
    (GraphIsomorphismHint.check_sound rawHint43 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint44 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso44 : rawGraph81 = rawGraph80 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph81Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph80Exponents)
    (GraphIsomorphismHint.check_sound rawHint44 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint45 : GraphIsomorphismHint where
  vertices := [0]
  edges := []
  swaps := []

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso45 : rawGraph82 = representatives 41 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph82Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph82Exponents)
    (GraphIsomorphismHint.check_sound rawHint45 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint46 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1, 2]
  swaps := [false, false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso46 : rawGraph83 = representatives 2 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence18Candidate rawIncidence18Valid rawGraph83Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence18Candidate rawIncidence18Valid rawGraph83Exponents)
    (GraphIsomorphismHint.check_sound rawHint46 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint47 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0, 2]
  swaps := [false, false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso47 : rawGraph84 = rawGraph83 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence19Candidate rawIncidence19Valid rawGraph84Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence18Candidate rawIncidence18Valid rawGraph83Exponents)
    (GraphIsomorphismHint.check_sound rawHint47 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint48 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso48 : rawGraph85 = representatives 19 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph85Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence4Candidate rawIncidence4Valid rawGraph85Exponents)
    (GraphIsomorphismHint.check_sound rawHint48 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint49 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso49 : rawGraph86 = representatives 23 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph86Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph86Exponents)
    (GraphIsomorphismHint.check_sound rawHint49 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint50 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso50 : rawGraph87 = representatives 28 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph87Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph87Exponents)
    (GraphIsomorphismHint.check_sound rawHint50 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint51 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso51 : rawGraph88 = representatives 27 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph88Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph88Exponents)
    (GraphIsomorphismHint.check_sound rawHint51 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint52 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso52 : rawGraph89 = representatives 24 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph89Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph89Exponents)
    (GraphIsomorphismHint.check_sound rawHint52 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint53 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso53 : rawGraph90 = representatives 39 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph90Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph90Exponents)
    (GraphIsomorphismHint.check_sound rawHint53 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint54 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1, 2]
  swaps := [false, false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso54 : rawGraph91 = representatives 3 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence20Candidate rawIncidence20Valid rawGraph91Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence20Candidate rawIncidence20Valid rawGraph91Exponents)
    (GraphIsomorphismHint.check_sound rawHint54 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint55 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1, 2]
  swaps := [false, true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso55 : rawGraph92 = rawGraph91 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence21Candidate rawIncidence21Valid rawGraph92Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence20Candidate rawIncidence20Valid rawGraph91Exponents)
    (GraphIsomorphismHint.check_sound rawHint55 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint56 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1, 2]
  swaps := [false, false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso56 : rawGraph93 = representatives 4 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph93Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph93Exponents)
    (GraphIsomorphismHint.check_sound rawHint56 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint57 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1, 2]
  swaps := [true, false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso57 : rawGraph94 = rawGraph91 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence23Candidate rawIncidence23Valid rawGraph94Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence20Candidate rawIncidence20Valid rawGraph91Exponents)
    (GraphIsomorphismHint.check_sound rawHint57 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint58 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1, 2]
  swaps := [true, true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso58 : rawGraph95 = rawGraph91 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence24Candidate rawIncidence24Valid rawGraph95Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence20Candidate rawIncidence20Valid rawGraph91Exponents)
    (GraphIsomorphismHint.check_sound rawHint58 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint59 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1, 2]
  swaps := [true, false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso59 : rawGraph96 = rawGraph93 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence25Candidate rawIncidence25Valid rawGraph96Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph93Exponents)
    (GraphIsomorphismHint.check_sound rawHint59 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint60 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0, 2]
  swaps := [false, false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso60 : rawGraph97 = rawGraph93 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence26Candidate rawIncidence26Valid rawGraph97Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph93Exponents)
    (GraphIsomorphismHint.check_sound rawHint60 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint61 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0, 2]
  swaps := [false, true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso61 : rawGraph98 = rawGraph93 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence27Candidate rawIncidence27Valid rawGraph98Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph93Exponents)
    (GraphIsomorphismHint.check_sound rawHint61 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint62 : GraphIsomorphismHint where
  vertices := [0, 1, 2]
  edges := [0, 1, 2]
  swaps := [false, false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso62 : rawGraph99 = representatives 5 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence28Candidate rawIncidence28Valid rawGraph99Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence28Candidate rawIncidence28Valid rawGraph99Exponents)
    (GraphIsomorphismHint.check_sound rawHint62 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint63 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso63 : rawGraph100 = representatives 16 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph100Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph100Exponents)
    (GraphIsomorphismHint.check_sound rawHint63 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint64 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso64 : rawGraph101 = representatives 20 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph101Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph101Exponents)
    (GraphIsomorphismHint.check_sound rawHint64 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint65 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso65 : rawGraph102 = representatives 17 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence9Candidate rawIncidence9Valid rawGraph102Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence9Candidate rawIncidence9Valid rawGraph102Exponents)
    (GraphIsomorphismHint.check_sound rawHint65 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint66 : GraphIsomorphismHint where
  vertices := [0, 1, 2]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso66 : rawGraph103 = representatives 15 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph103Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph103Exponents)
    (GraphIsomorphismHint.check_sound rawHint66 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint67 : GraphIsomorphismHint where
  vertices := [2, 1, 0]
  edges := [1, 0]
  swaps := [true, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso67 : rawGraph104 = rawGraph103 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph104Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph103Exponents)
    (GraphIsomorphismHint.check_sound rawHint67 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint68 : GraphIsomorphismHint where
  vertices := [1, 0, 2]
  edges := [1, 0]
  swaps := [false, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso68 : rawGraph105 = rawGraph103 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence11Candidate rawIncidence11Valid rawGraph105Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph103Exponents)
    (GraphIsomorphismHint.check_sound rawHint68 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint69 : GraphIsomorphismHint where
  vertices := [1, 2, 0]
  edges := [0, 1]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso69 : rawGraph106 = rawGraph103 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence11Candidate rawIncidence11Valid rawGraph106Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph103Exponents)
    (GraphIsomorphismHint.check_sound rawHint69 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint70 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso70 : rawGraph107 = rawGraph102 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph107Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence9Candidate rawIncidence9Valid rawGraph102Exponents)
    (GraphIsomorphismHint.check_sound rawHint70 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint71 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0, 1]
  swaps := [false, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso71 : rawGraph108 = rawGraph102 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph108Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence9Candidate rawIncidence9Valid rawGraph102Exponents)
    (GraphIsomorphismHint.check_sound rawHint71 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint72 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 1]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso72 : rawGraph109 = representatives 18 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph109Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph109Exponents)
    (GraphIsomorphismHint.check_sound rawHint72 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint73 : GraphIsomorphismHint where
  vertices := [0, 2, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso73 : rawGraph110 = rawGraph103 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph110Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph103Exponents)
    (GraphIsomorphismHint.check_sound rawHint73 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint74 : GraphIsomorphismHint where
  vertices := [2, 0, 1]
  edges := [0, 1]
  swaps := [true, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso74 : rawGraph111 = rawGraph103 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph111Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph103Exponents)
    (GraphIsomorphismHint.check_sound rawHint74 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint75 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso75 : rawGraph112 = rawGraph86 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph112Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph86Exponents)
    (GraphIsomorphismHint.check_sound rawHint75 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint76 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso76 : rawGraph113 = representatives 22 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph113Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph113Exponents)
    (GraphIsomorphismHint.check_sound rawHint76 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint77 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso77 : rawGraph114 = rawGraph88 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph114Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph88Exponents)
    (GraphIsomorphismHint.check_sound rawHint77 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint78 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso78 : rawGraph115 = rawGraph87 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph115Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph87Exponents)
    (GraphIsomorphismHint.check_sound rawHint78 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint79 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso79 : rawGraph116 = representatives 25 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph116Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph116Exponents)
    (GraphIsomorphismHint.check_sound rawHint79 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint80 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso80 : rawGraph117 = rawGraph116 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph117Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph116Exponents)
    (GraphIsomorphismHint.check_sound rawHint80 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint81 : GraphIsomorphismHint where
  vertices := [0, 1, 2]
  edges := [0, 1, 2]
  swaps := [false, false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso81 : rawGraph118 = representatives 6 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence29Candidate rawIncidence29Valid rawGraph118Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence29Candidate rawIncidence29Valid rawGraph118Exponents)
    (GraphIsomorphismHint.check_sound rawHint81 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint82 : GraphIsomorphismHint where
  vertices := [0, 1, 2]
  edges := [0, 2, 1]
  swaps := [false, false, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso82 : rawGraph119 = rawGraph118 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence30Candidate rawIncidence30Valid rawGraph119Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence29Candidate rawIncidence29Valid rawGraph118Exponents)
    (GraphIsomorphismHint.check_sound rawHint82 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint83 : GraphIsomorphismHint where
  vertices := [0, 2, 1]
  edges := [0, 2, 1]
  swaps := [true, false, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso83 : rawGraph120 = rawGraph99 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence31Candidate rawIncidence31Valid rawGraph120Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence28Candidate rawIncidence28Valid rawGraph99Exponents)
    (GraphIsomorphismHint.check_sound rawHint83 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint84 : GraphIsomorphismHint where
  vertices := [2, 0, 1]
  edges := [0, 2, 1]
  swaps := [false, false, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso84 : rawGraph121 = rawGraph99 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence32Candidate rawIncidence32Valid rawGraph121Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence28Candidate rawIncidence28Valid rawGraph99Exponents)
    (GraphIsomorphismHint.check_sound rawHint84 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint85 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0, 1]
  swaps := [false, true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso85 : rawGraph122 = rawGraph109 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph122Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph109Exponents)
    (GraphIsomorphismHint.check_sound rawHint85 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint86 : GraphIsomorphismHint where
  vertices := [0]
  edges := []
  swaps := []

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso86 : rawGraph123 = representatives 43 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph123Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph123Exponents)
    (GraphIsomorphismHint.check_sound rawHint86 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint87 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0, 2, 1]
  swaps := [false, true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso87 : rawGraph124 = rawGraph93 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence33Candidate rawIncidence33Valid rawGraph124Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence22Candidate rawIncidence22Valid rawGraph93Exponents)
    (GraphIsomorphismHint.check_sound rawHint87 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint88 : GraphIsomorphismHint where
  vertices := [0, 2, 1]
  edges := [2, 1, 0]
  swaps := [false, false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso88 : rawGraph125 = rawGraph118 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence34Candidate rawIncidence34Valid rawGraph125Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence29Candidate rawIncidence29Valid rawGraph118Exponents)
    (GraphIsomorphismHint.check_sound rawHint88 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint89 : GraphIsomorphismHint where
  vertices := [2, 0, 1]
  edges := [1, 2, 0]
  swaps := [true, true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso89 : rawGraph126 = rawGraph118 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence35Candidate rawIncidence35Valid rawGraph126Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence29Candidate rawIncidence29Valid rawGraph118Exponents)
    (GraphIsomorphismHint.check_sound rawHint89 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint90 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso90 : rawGraph127 = rawGraph100 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph127Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph100Exponents)
    (GraphIsomorphismHint.check_sound rawHint90 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint91 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 0]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso91 : rawGraph128 = rawGraph109 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence15Candidate rawIncidence15Valid rawGraph128Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph109Exponents)
    (GraphIsomorphismHint.check_sound rawHint91 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint92 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso92 : rawGraph129 = rawGraph101 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph129Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph101Exponents)
    (GraphIsomorphismHint.check_sound rawHint92 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint93 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 0]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso93 : rawGraph130 = rawGraph101 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph130Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph101Exponents)
    (GraphIsomorphismHint.check_sound rawHint93 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint94 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso94 : rawGraph131 = rawGraph109 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph131Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence13Candidate rawIncidence13Valid rawGraph109Exponents)
    (GraphIsomorphismHint.check_sound rawHint94 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint95 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 0]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso95 : rawGraph132 = rawGraph100 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph132Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph100Exponents)
    (GraphIsomorphismHint.check_sound rawHint95 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint96 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso96 : rawGraph133 = representatives 21 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph133Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph133Exponents)
    (GraphIsomorphismHint.check_sound rawHint96 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint97 : GraphIsomorphismHint where
  vertices := [0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso97 : rawGraph134 = rawGraph133 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph134Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence1Candidate rawIncidence1Valid rawGraph133Exponents)
    (GraphIsomorphismHint.check_sound rawHint97 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint98 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso98 : rawGraph135 = representatives 29 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph135Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph135Exponents)
    (GraphIsomorphismHint.check_sound rawHint98 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint99 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso99 : rawGraph136 = representatives 35 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph136Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph136Exponents)
    (GraphIsomorphismHint.check_sound rawHint99 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint100 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0]
  swaps := [false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso100 : rawGraph137 = representatives 26 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph137Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph137Exponents)
    (GraphIsomorphismHint.check_sound rawHint100 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint101 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso101 : rawGraph138 = rawGraph137 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph138Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph137Exponents)
    (GraphIsomorphismHint.check_sound rawHint101 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint102 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [0, 2, 1]
  swaps := [false, false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso102 : rawGraph139 = rawGraph83 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence36Candidate rawIncidence36Valid rawGraph139Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence18Candidate rawIncidence18Valid rawGraph83Exponents)
    (GraphIsomorphismHint.check_sound rawHint102 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint103 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 2, 0]
  swaps := [false, true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso103 : rawGraph140 = rawGraph83 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence37Candidate rawIncidence37Valid rawGraph140Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence18Candidate rawIncidence18Valid rawGraph83Exponents)
    (GraphIsomorphismHint.check_sound rawHint103 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint104 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso104 : rawGraph141 = rawGraph135 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph141Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph135Exponents)
    (GraphIsomorphismHint.check_sound rawHint104 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint105 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [0]
  swaps := [true]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso105 : rawGraph142 = rawGraph136 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence2Candidate rawIncidence2Valid rawGraph142Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence3Candidate rawIncidence3Valid rawGraph136Exponents)
    (GraphIsomorphismHint.check_sound rawHint105 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint106 : GraphIsomorphismHint where
  vertices := [0, 2, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso106 : rawGraph143 = rawGraph54 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence10Candidate rawIncidence10Valid rawGraph143Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence6Candidate rawIncidence6Valid rawGraph54Exponents)
    (GraphIsomorphismHint.check_sound rawHint106 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint107 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 0]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso107 : rawGraph144 = rawGraph51 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence12Candidate rawIncidence12Valid rawGraph144Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence5Candidate rawIncidence5Valid rawGraph51Exponents)
    (GraphIsomorphismHint.check_sound rawHint107 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint108 : GraphIsomorphismHint where
  vertices := [0, 1]
  edges := [1, 0]
  swaps := [false, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso108 : rawGraph145 = rawGraph64 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence14Candidate rawIncidence14Valid rawGraph145Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph64Exponents)
    (GraphIsomorphismHint.check_sound rawHint108 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint109 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 0]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso109 : rawGraph146 = rawGraph63 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence16Candidate rawIncidence16Valid rawGraph146Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence8Candidate rawIncidence8Valid rawGraph63Exponents)
    (GraphIsomorphismHint.check_sound rawHint109 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Proposed finite vertex, edge and ordered branch maps. -/
def rawHint110 : GraphIsomorphismHint where
  vertices := [1, 0]
  edges := [1, 0]
  swaps := [true, false]

/-- A checked decorated isomorphism identifies these actual source strata. -/
theorem rawGraphIso110 : rawGraph147 = rawGraph62 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence17Candidate rawIncidence17Valid rawGraph147Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence7Candidate rawIncidence7Valid rawGraph62Exponents)
    (GraphIsomorphismHint.check_sound rawHint110 _ _
      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))

/-- Every occurrence selects one fixed representative; no term is dropped. -/
def index_1_2 : Fin 122 → Fin 44 :=
  ![37,
    31,
    31,
    42,
    1,
    0,
    0,
    0,
    0,
    36,
    30,
    33,
    32,
    11,
    10,
    10,
    13,
    14,
    14,
    36,
    34,
    32,
    33,
    30,
    11,
    13,
    7,
    12,
    8,
    9,
    9,
    40,
    1,
    0,
    7,
    8,
    11,
    13,
    9,
    10,
    13,
    11,
    9,
    14,
    14,
    10,
    12,
    34,
    38,
    38,
    41,
    2,
    2,
    19,
    23,
    28,
    27,
    24,
    39,
    3,
    3,
    3,
    3,
    4,
    4,
    3,
    3,
    3,
    3,
    4,
    4,
    4,
    4,
    4,
    4,
    5,
    16,
    20,
    17,
    15,
    15,
    15,
    15,
    17,
    17,
    18,
    15,
    15,
    23,
    22,
    27,
    28,
    25,
    25,
    6,
    6,
    5,
    5,
    16,
    18,
    20,
    43,
    4,
    6,
    6,
    19,
    16,
    18,
    20,
    20,
    18,
    16,
    21,
    21,
    29,
    35,
    26,
    26,
    2,
    2,
    29,
    35]

/-- Every lookup is bound to the complete previously decoded column vector. -/
theorem columns_1_2_eq :
    ∀ i, raw12Degree3Columns i = representatives (index_1_2 i) := by
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
  · exact rawGraphIso13
  · exact rawGraphIso24
  · exact rawGraphIso25
  · exact rawGraphIso26
  · exact rawGraphIso27
  · exact rawGraphIso28
  · exact rawGraphIso29
  · exact rawGraphIso30
  · exact rawGraphIso4
  · exact rawGraphIso5
  · exact rawGraphIso25
  · exact rawGraphIso27
  · exact rawGraphIso31
  · exact rawGraphIso32
  · exact rawGraphIso33
  · exact rawGraphIso34
  · exact rawGraphIso35
  · exact rawGraphIso36
  · exact rawGraphIso37
  · exact rawGraphIso38
  · exact rawGraphIso39
  · exact rawGraphIso40
  · exact rawGraphIso41
  · exact rawGraphIso42
  · exact rawGraphIso43
  · exact rawGraphIso44
  · exact rawGraphIso45
  · exact rawGraphIso46
  · exact rawGraphIso47
  · exact rawGraphIso48
  · exact rawGraphIso49
  · exact rawGraphIso50
  · exact rawGraphIso51
  · exact rawGraphIso52
  · exact rawGraphIso53
  · exact rawGraphIso54
  · exact rawGraphIso54
  · exact rawGraphIso55
  · exact rawGraphIso55
  · exact rawGraphIso56
  · exact rawGraphIso56
  · exact rawGraphIso57
  · exact rawGraphIso57
  · exact rawGraphIso58
  · exact rawGraphIso58
  · exact rawGraphIso59
  · exact rawGraphIso59
  · exact rawGraphIso60
  · exact rawGraphIso60
  · exact rawGraphIso61
  · exact rawGraphIso61
  · exact rawGraphIso62
  · exact rawGraphIso63
  · exact rawGraphIso64
  · exact rawGraphIso65
  · exact rawGraphIso66
  · exact rawGraphIso67
  · exact rawGraphIso68
  · exact rawGraphIso69
  · exact rawGraphIso70
  · exact rawGraphIso71
  · exact rawGraphIso72
  · exact rawGraphIso73
  · exact rawGraphIso74
  · exact rawGraphIso75
  · exact rawGraphIso76
  · exact rawGraphIso77
  · exact rawGraphIso78
  · exact rawGraphIso79
  · exact rawGraphIso80
  · exact rawGraphIso81
  · exact rawGraphIso82
  · exact rawGraphIso83
  · exact rawGraphIso84
  · exact rawGraphIso63
  · exact rawGraphIso85
  · exact rawGraphIso64
  · exact rawGraphIso86
  · exact rawGraphIso87
  · exact rawGraphIso88
  · exact rawGraphIso89
  · exact rawGraphIso48
  · exact rawGraphIso90
  · exact rawGraphIso91
  · exact rawGraphIso92
  · exact rawGraphIso93
  · exact rawGraphIso94
  · exact rawGraphIso95
  · exact rawGraphIso96
  · exact rawGraphIso97
  · exact rawGraphIso98
  · exact rawGraphIso99
  · exact rawGraphIso100
  · exact rawGraphIso101
  · exact rawGraphIso102
  · exact rawGraphIso103
  · exact rawGraphIso104
  · exact rawGraphIso105

/-- All coefficients from the actual input coordinate vector, with repetitions. -/
def grouped_1_2 : RelationCertificate.Coordinates 44 :=
  ∑ i, Pi.single (index_1_2 i) (raw12Degree3Coordinates i)

/-- Exact rational sums agree at every one of the 44 held coordinates. -/
theorem grouped_1_2_eq : grouped_1_2 = collectedCoordinates := by
  funext i
  fin_cases i <;> decide +kernel

/-- Every occurrence selects one fixed representative; no term is dropped. -/
def index_2_1 : Fin 108 → Fin 44 :=
  ![37,
    31,
    31,
    32,
    42,
    1,
    0,
    0,
    0,
    0,
    36,
    33,
    30,
    11,
    9,
    11,
    13,
    14,
    10,
    10,
    10,
    13,
    14,
    14,
    36,
    34,
    30,
    33,
    11,
    13,
    7,
    12,
    8,
    9,
    9,
    40,
    1,
    0,
    8,
    12,
    7,
    34,
    38,
    38,
    28,
    41,
    2,
    2,
    19,
    15,
    15,
    23,
    27,
    24,
    39,
    3,
    3,
    3,
    3,
    4,
    4,
    3,
    3,
    3,
    3,
    4,
    4,
    4,
    4,
    4,
    4,
    5,
    16,
    20,
    20,
    17,
    18,
    16,
    17,
    17,
    18,
    15,
    15,
    23,
    22,
    21,
    27,
    25,
    25,
    26,
    6,
    6,
    5,
    5,
    16,
    18,
    20,
    43,
    4,
    6,
    6,
    19,
    29,
    35,
    2,
    2,
    29,
    35]

/-- Every lookup is bound to the complete previously decoded column vector. -/
theorem columns_2_1_eq :
    ∀ i, raw21Degree3Columns i = representatives (index_2_1 i) := by
  intro i
  fin_cases i
  · exact rawGraphIso0
  · exact rawGraphIso1
  · exact rawGraphIso2
  · exact rawGraphIso12
  · exact rawGraphIso3
  · exact rawGraphIso4
  · exact rawGraphIso5
  · exact rawGraphIso6
  · exact rawGraphIso7
  · exact rawGraphIso8
  · exact rawGraphIso9
  · exact rawGraphIso22
  · exact rawGraphIso23
  · exact rawGraphIso13
  · exact rawGraphIso29
  · exact rawGraphIso31
  · exact rawGraphIso35
  · exact rawGraphIso106
  · exact rawGraphIso107
  · exact rawGraphIso14
  · exact rawGraphIso15
  · exact rawGraphIso16
  · exact rawGraphIso17
  · exact rawGraphIso18
  · exact rawGraphIso19
  · exact rawGraphIso20
  · exact rawGraphIso10
  · exact rawGraphIso11
  · exact rawGraphIso13
  · exact rawGraphIso24
  · exact rawGraphIso25
  · exact rawGraphIso26
  · exact rawGraphIso27
  · exact rawGraphIso28
  · exact rawGraphIso29
  · exact rawGraphIso30
  · exact rawGraphIso4
  · exact rawGraphIso8
  · exact rawGraphIso108
  · exact rawGraphIso109
  · exact rawGraphIso110
  · exact rawGraphIso42
  · exact rawGraphIso43
  · exact rawGraphIso44
  · exact rawGraphIso50
  · exact rawGraphIso45
  · exact rawGraphIso46
  · exact rawGraphIso47
  · exact rawGraphIso48
  · exact rawGraphIso67
  · exact rawGraphIso69
  · exact rawGraphIso49
  · exact rawGraphIso77
  · exact rawGraphIso52
  · exact rawGraphIso53
  · exact rawGraphIso54
  · exact rawGraphIso54
  · exact rawGraphIso55
  · exact rawGraphIso55
  · exact rawGraphIso56
  · exact rawGraphIso56
  · exact rawGraphIso57
  · exact rawGraphIso57
  · exact rawGraphIso58
  · exact rawGraphIso58
  · exact rawGraphIso59
  · exact rawGraphIso59
  · exact rawGraphIso60
  · exact rawGraphIso60
  · exact rawGraphIso61
  · exact rawGraphIso61
  · exact rawGraphIso62
  · exact rawGraphIso63
  · exact rawGraphIso64
  · exact rawGraphIso92
  · exact rawGraphIso65
  · exact rawGraphIso94
  · exact rawGraphIso95
  · exact rawGraphIso70
  · exact rawGraphIso71
  · exact rawGraphIso72
  · exact rawGraphIso73
  · exact rawGraphIso74
  · exact rawGraphIso75
  · exact rawGraphIso76
  · exact rawGraphIso97
  · exact rawGraphIso51
  · exact rawGraphIso79
  · exact rawGraphIso80
  · exact rawGraphIso101
  · exact rawGraphIso81
  · exact rawGraphIso82
  · exact rawGraphIso83
  · exact rawGraphIso84
  · exact rawGraphIso63
  · exact rawGraphIso85
  · exact rawGraphIso64
  · exact rawGraphIso86
  · exact rawGraphIso87
  · exact rawGraphIso88
  · exact rawGraphIso89
  · exact rawGraphIso48
  · exact rawGraphIso98
  · exact rawGraphIso99
  · exact rawGraphIso102
  · exact rawGraphIso103
  · exact rawGraphIso104
  · exact rawGraphIso105

/-- All coefficients from the actual input coordinate vector, with repetitions. -/
def grouped_2_1 : RelationCertificate.Coordinates 44 :=
  ∑ i, Pi.single (index_2_1 i) (raw21Degree3Coordinates i)

/-- Exact rational sums agree at every one of the 44 held coordinates. -/
theorem grouped_2_1_eq : grouped_2_1 = collectedCoordinates := by
  funext i
  fin_cases i <;> decide +kernel

/-- Repeated isomorphic columns regroup by linearity in the existing free module. -/
theorem interpret_grouped {m n : ℕ}
    (columns : Fin m → TautologicalStratum 2 (Fin 1))
    (frame : Fin n → TautologicalStratum 2 (Fin 1))
    (index : Fin m → Fin n) (coordinates : RelationCertificate.Coordinates m)
    (hc : ∀ i, columns i = frame (index i)) :
    RelationCertificate.interpret columns coordinates =
      RelationCertificate.interpret frame
        (∑ i, Pi.single (index i) (coordinates i)) := by
  classical
  calc
    RelationCertificate.interpret columns coordinates =
        ∑ i, coordinates i • StrataModule.basis (columns i) := rfl
    _ = ∑ i, coordinates i • StrataModule.basis (frame (index i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc i]
    _ = RelationCertificate.interpret frame
        (∑ i, Pi.single (index i) (coordinates i)) := by
      simp only [map_sum, RelationCertificate.interpret,
        Fintype.linearCombination_apply_single]

/-- The first complete raw expression has the certified collected coordinates. -/
theorem raw_1_2_eq_collected : raw12Degree3 =
    RelationCertificate.interpret representatives collectedCoordinates := by
  calc
    raw12Degree3 = RelationCertificate.interpret representatives grouped_1_2 :=
      interpret_grouped _ _ _ _ columns_1_2_eq
    _ = _ := congrArg (RelationCertificate.interpret representatives) grouped_1_2_eq

/-- The second complete raw expression has the same certified coordinates. -/
theorem raw_2_1_eq_collected : raw21Degree3 =
    RelationCertificate.interpret representatives collectedCoordinates := by
  calc
    raw21Degree3 = RelationCertificate.interpret representatives grouped_2_1 :=
      interpret_grouped _ _ _ _ columns_2_1_eq
    _ = _ := congrArg (RelationCertificate.interpret representatives) grouped_2_1_eq

/-- These two actual finite raw sums agree before imposing tautological relations. -/
theorem raw_ordered_degree3_equal : raw12Degree3 = raw21Degree3 :=
  raw_1_2_eq_collected.trans raw_2_1_eq_collected.symm

end AxiomaticGW.AdmcyclesHodgeStrataIsomorphisms
