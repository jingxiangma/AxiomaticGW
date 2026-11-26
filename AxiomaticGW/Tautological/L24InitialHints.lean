/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24InitialGraphs
public import AxiomaticGW.Tautological.L24Initial
public import AxiomaticGW.Tautological.CotangentDimensionReplay

/-!
# Candidate graph destinations for the BP initial row

A small numeric key only selects a proposed destination and finite bijections.
It is not an isomorphism test: every retained term must separately pass all
incidence, genus, kappa and cotangent checks. Missing keys return an invalid
empty hint. Collisions cannot supply a proof of graph coverage.
-/

@[expose] public section

namespace AxiomaticGW.L24InitialHints
open RelationCertificate

set_option maxRecDepth 20000

/-- Quick incidence and cotangent key, with no mathematical authority on its own. -/
def graphKey (G : DecoratedStableGraph (Fin 4)) : ℕ :=
  ([G.graph.vertexCount, G.graph.edgeCount] ++
    (List.finRange G.graph.vertexCount).map G.graph.genus ++
    (List.finRange 4).map (fun i ↦ (G.graph.legVertex i).val) ++
    (List.finRange G.graph.edgeCount).flatMap
      (fun e ↦ [(G.graph.endpoint e 0).val, (G.graph.endpoint e 1).val]) ++
    (List.finRange 4).map G.legPsiPower ++
    (List.finRange G.graph.edgeCount).flatMap
      (fun e ↦ [G.halfEdgePsiPower e 0, G.halfEdgePsiPower e 1])).foldl
        (fun h n ↦ (h * 37 + n + 1) % 2147483647) 0

/-- An untrusted candidate table; full graph coverage supplies its meaning. -/
def lookupKey (k : ℕ) : Fin 860 × GraphIsomorphismHint :=
  (if k < 1116840685 then (if k < 569214074 then (if k < 284035466 then (if k < 150987506 then
    (if k < 72231694 then (if k < 30144268 then (if k < 16857787 then (if k < 5790365 then (if k
    = 4761898 then ⟨362, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k <
    10984042 then (if k = 5790365 then ⟨342, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩) else (if k = 10984042 then ⟨289, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩))) else (if k < 18310432 then (if k = 16857787 then ⟨347, ⟨[0, 1, 2], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 18870987 then (if k = 18310432 then
    ⟨149, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 18870987 then
    ⟨263, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 59512534
    then (if k < 40702151 then (if k = 30144268 then ⟨341, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k < 46110000 then (if k = 40702151 then ⟨231, ⟨[2, 1, 0],
    [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 46110000 then ⟨336, ⟨[2, 1, 0],
    [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 61520984 then (if k = 59512534
    then ⟨512, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 65056054
    then (if k = 61520984 then ⟨297, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k = 65056054 then ⟨226, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩))))) else (if k < 113579796 then (if k < 86340783 then (if k < 83517710 then (if k =
    72231694 then ⟨361, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k <
    84030772 then (if k = 83517710 then ⟨558, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩) else (if k = 84030772 then ⟨608, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩))) else (if k < 102869086 then (if k = 86340783 then ⟨262, ⟨[1, 2, 0], [1, 0],
    [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 108384675 then (if k = 102869086 then
    ⟨293, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 108384675
    then ⟨607, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k <
    138102784 then (if k < 126982330 then (if k = 113579796 then ⟨338, ⟨[2, 1, 0], [1, 0],
    [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 128990780 then (if k = 126982330 then
    ⟨511, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 128990780 then
    ⟨299, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 143510633
    then (if k < 140111234 then (if k = 138102784 then ⟨527, ⟨[1, 0], [0, 1], [false, true]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k = 140111234 then ⟨843, ⟨[0, 1, 2], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 144442764 then (if k = 143510633 then ⟨657,
    ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 144442764 then ⟨91,
    ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))))) else (if k < 220315269 then
    (if k < 199591095 then (if k < 170338882 then (if k < 162456687 then (if k = 150987506 then
    ⟨560, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 164465137 then
    (if k = 162456687 then ⟨524, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else
    (if k = 164465137 then ⟨286, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))
    else (if k < 180752781 then (if k = 170338882 then ⟨292, ⟨[0, 1, 2], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 190087621 then (if k = 180752781 then ⟨647,
    ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 190087621 then ⟨367,
    ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 210980429 then
    (if k < 200269719 then (if k = 199591095 then ⟨359, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k < 205106684 then (if k = 200269719 then ⟨611, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 205106684 then ⟨646, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 212084347 then (if k < 211912560
    then (if k = 210980429 then ⟨656, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k = 211912560 then ⟨90, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))
    else (if k < 214441524 then (if k = 212084347 then ⟨595, ⟨[0, 1], [0, 1], [false, false]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k = 214441524 then ⟨370, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩))))) else (if k < 247669515 then (if k < 244516345 then (if k <
    236438250 then (if k = 220315269 then ⟨851, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩) else (if k < 237511867 then (if k = 236438250 then ⟨594, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 237511867 then ⟨604, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 245796723 then (if k = 244516345 then ⟨255,
    ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 245846007 then (if k
    = 245796723 then ⟨47, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 245846007
    then ⟨46, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 267060891 then (if
    k < 256350181 then (if k = 247669515 then ⟨45, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k < 261865770 then (if k = 256350181 then ⟨326, ⟨[0, 1, 2], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 261865770 then ⟨603, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 267814966 then (if k < 267739515 then (if k
    = 267060891 then ⟨357, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    = 267739515 then ⟨610, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k
    < 281758493 then (if k = 267814966 then ⟨577, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 281758493 then ⟨249, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩))))))) else (if k < 435239588 then (if k < 346405216 then (if k <
    311986141 then (if k < 299890252 then (if k < 284086082 then (if k = 284035466 then ⟨816,
    ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 296991728 then (if k = 284086082
    then ⟨6, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 296991728 then ⟨652,
    ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 306112396 then (if
    k = 299890252 then ⟨177, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if
    k < 306326568 then (if k = 306112396 then ⟨248, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 306326568 then ⟨853, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩)))) else (if k < 324408490 then (if k < 315139311 then (if k = 311986141 then
    ⟨258, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 323819977 then
    (if k = 315139311 then ⟨44, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k =
    323819977 then ⟨328, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if
    k < 325272622 then (if k = 324408490 then ⟨302, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k < 335284762 then (if k = 325272622 then ⟨164, ⟨[1, 2, 0], [1,
    0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 335284762 then ⟨575, ⟨[0, 1], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))) else (if k < 370759119 then (if k <
    353379386 then (if k < 348762393 then (if k = 346405216 then ⟨561, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 353328770 then (if k = 348762393 then ⟨300,
    ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 353328770 then
    ⟨815, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 364461524 then (if k =
    353379386 then ⟨5, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 367360048
    then (if k = 364461524 then ⟨653, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k = 367360048 then ⟨176, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩)))) else (if k < 390110495 then (if k < 378480502 then (if k = 370759119 then ⟨563,
    ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 383888351 then (if k
    = 378480502 then ⟨122, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if
    k = 383888351 then ⟨329, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else
    (if k < 421296061 then (if k < 402834405 then (if k = 390110495 then ⟨348, ⟨[0, 1, 2], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 402834405 then ⟨121, ⟨[1, 2, 0],
    [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 431312597 then (if k =
    421296061 then ⟨571, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k =
    431312597 then ⟨617, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))))) else (if
    k < 499886311 then (if k < 462644163 then (if k < 451358147 then (if k < 440647437 then (if
    k = 435239588 then ⟨261, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else
    (if k < 445484402 then (if k = 440647437 then ⟨306, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k = 445484402 then ⟨363, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 459593491 then (if k = 451358147 then ⟨331, ⟨[2, 1,
    0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 462478601 then (if k =
    459593491 then ⟨260, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    = 462478601 then ⟨339, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else
    (if k < 482221115 then (if k < 475881135 then (if k = 462644163 then ⟨567, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 477889585 then (if k = 475881135 then
    ⟨510, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 477889585 then
    ⟨298, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 488765857
    then (if k < 486832504 then (if k = 482221115 then ⟨73, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k = 486832504 then ⟨337, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 498782393 then (if k = 488765857 then ⟨573, ⟨[0, 1],
    [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 498782393 then ⟨616, ⟨[0, 1],
    [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))) else (if k < 524240214 then (if k <
    506108783 then (if k < 500235038 then (if k = 499886311 then ⟨557, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 502243488 then (if k = 500235038 then ⟨513,
    ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 502243488 then ⟨296,
    ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 508117233 then
    (if k = 506108783 then ⟨505, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else
    (if k < 519237687 then (if k = 508117233 then ⟨305, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k = 519237687 then ⟨291, ⟨[0, 1, 2], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 543591590 then (if k < 530113959 then (if k
    = 524240214 then ⟨559, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    < 537369446 then (if k = 530113959 then ⟨566, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 537369446 then ⟨352, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩))) else (if k < 551478535 then (if k < 549690911 then (if k = 543591590 then
    ⟨294, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 549690911
    then ⟨72, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 559879234
    then (if k = 551478535 then ⟨270, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k = 559879234 then ⟨655, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩)))))))) else (if k < 847681198 then (if k < 708537470 then (if k < 618948331 then (if k
    < 604839242 then (if k < 585165268 then (if k < 574968306 then (if k = 569214074 then ⟨365,
    ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 584233137 then (if k
    = 574968306 then ⟨842, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if
    k = 584233137 then ⟨654, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else
    (if k < 592120082 then (if k = 585165268 then ⟨89, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k < 593567977 then (if k = 592120082 then ⟨508, ⟨[1, 0], [0, 1],
    [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 593567977 then ⟨850, ⟨[2, 1, 0], [1,
    0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 610304905 then (if k < 608432113
    then (if k = 604839242 then ⟨350, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k < 608481397 then (if k = 608432113 then ⟨12, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩) else (if k = 608481397 then ⟨11, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))
    else (if k < 615959696 then (if k = 610304905 then ⟨819, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 616638320 then (if k = 615959696 then ⟨360, ⟨[2, 1, 0], [1, 0],
    [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 616638320 then ⟨613, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))) else (if k < 671690315 then (if k < 640313599
    then (if k < 629040318 then (if k = 618948331 then ⟨267, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k < 635141655 then (if k = 629040318 then ⟨222, ⟨[1, 2, 0],
    [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 635141655 then ⟨57, ⟨[2, 1, 0],
    [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 640992223 then (if k =
    640313599 then ⟨358, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k <
    660884946 then (if k = 640992223 then ⟨612, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩) else (if k = 660884946 then ⟨837, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩)))) else (if k < 684183567 then (if k < 676118181 then (if k = 671690315 then ⟨310,
    ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 677774701 then (if
    k = 676118181 then ⟨661, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if
    k = 677774701 then ⟨14, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k <
    696510114 then (if k < 685238849 then (if k = 684183567 then ⟨576, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 685238849 then ⟨254, ⟨[2, 1, 0], [1, 0],
    [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 697072685 then (if k = 696510114 then
    ⟨221, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 697072685
    then ⟨327, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))))) else (if k <
    769090948 then (if k < 737714232 then (if k < 716258853 then (if k < 713038417 then (if k =
    708537470 then ⟨574, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k <
    713360329 then (if k = 713038417 then ⟨853, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 713360329 then ⟨651, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩))) else (if k < 722695169 then (if k = 716258853 then ⟨836, ⟨[2, 1, 0], [1,
    0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 726440951 then (if k = 722695169
    then ⟨366, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 726440951
    then ⟨547, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k <
    743587977 then (if k < 739160111 then (if k = 737714232 then ⟨650, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 740612756 then (if k = 739160111 then ⟨309,
    ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 740612756 then
    ⟨180, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 747049072
    then (if k < 746486501 then (if k = 743587977 then ⟨660, ⟨[0, 1], [0, 1], [false, false]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k = 746486501 then ⟨151, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 763014804 then (if k = 747049072 then ⟨852, ⟨[2, 1,
    0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 763014804 then ⟨326, ⟨[2, 1,
    0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))) else (if k < 810439050 then (if k <
    795919197 then (if k < 788622750 then (if k = 769090948 then ⟨633, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 793910747 then (if k = 788622750 then ⟨64,
    ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 793910747 then ⟨546,
    ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 800256952 then (if k
    = 795919197 then ⟨840, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if
    k < 800422514 then (if k = 800256952 then ⟨330, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 800422514 then ⟨580, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩)))) else (if k < 830484600 then (if k < 819773890 then (if k = 810439050 then
    ⟨625, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 824610855 then
    (if k = 819773890 then ⟨359, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k = 824610855 then ⟨332, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩))) else (if k < 836560744 then (if k < 832497800 then (if k = 830484600 then ⟨328, ⟨[2,
    1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 832497800 then ⟨166, ⟨[2,
    1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 837664662 then (if k =
    836560744 then ⟨632, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k =
    837664662 then ⟨572, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))))) else
    (if k < 991336907 then (if k < 898589716 then (if k < 877908846 then (if k < 862018565 then
    (if k < 854328964 then (if k = 847681198 then ⟨614, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k < 857016038 then (if k = 854328964 then ⟨128, ⟨[2, 1, 0], [1,
    0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 857016038 then ⟨307, ⟨[0, 1, 2], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 867892310 then (if k = 862018565
    then ⟨570, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 872035101
    then (if k = 867892310 then ⟨579, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k = 872035101 then ⟨615, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩)))) else (if k < 879361491 then (if k < 878682867 then (if k = 877908846 then ⟨623,
    ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 879012764 then (if k
    = 878682867 then ⟨127, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    = 879012764 then ⟨565, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if
    k < 881369941 then (if k = 879361491 then ⟨504, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 887243686 then (if k = 881369941 then ⟨304, ⟨[0, 1, 2], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 887243686 then ⟨357, ⟨[0, 1, 2], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))) else (if k < 953738047 then (if k <
    928817364 then (if k < 903366667 then (if k = 898589716 then ⟨71, ⟨[2, 1, 0], [1, 0], [true,
    true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 916495899 then (if k = 903366667 then ⟨568,
    ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 916495899 then ⟨293,
    ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 933989308 then (if
    k = 928817364 then ⟨831, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if
    k < 934743383 then (if k = 933989308 then ⟨851, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k = 934743383 then ⟨857, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 967847136 then (if k < 963920145 then (if k = 953738047
    then ⟨351, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 966818669
    then (if k = 963920145 then ⟨619, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k = 966818669 then ⟨172, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩))) else (if k < 978091950 then (if k < 973254985 then (if k = 967847136 then ⟨838, ⟨[2,
    1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 973254985 then ⟨336, ⟨[0,
    1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 983965695 then (if k =
    978091950 then ⟨353, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k =
    983965695 then ⟨292, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))))) else
    (if k < 1049638578 then (if k < 1032842586 then (if k < 1015690810 then (if k < 992201039
    then (if k = 991336907 then ⟨277, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k < 1014828663 then (if k = 992201039 then ⟨266, ⟨[2, 1, 0], [1, 0], [true,
    true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1014828663 then ⟨833, ⟨[2, 1, 0], [1, 0],
    [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1031389941 then (if k = 1015690810
    then ⟨841, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k <
    1031465392 then (if k = 1031389941 then ⟨621, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 1031465392 then ⟨585, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩)))) else (if k < 1040724781 then (if k < 1034288465 then (if k = 1032842586
    then ⟨507, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1036659827
    then (if k = 1034288465 then ⟨171, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k = 1036659827 then ⟨50, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩))) else (if k < 1049589294 then (if k < 1045408919 then (if k = 1040724781 then ⟨338,
    ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1045408919 then
    ⟨223, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 1049590626
    then (if k = 1049589294 then ⟨43, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    = 1049590626 then ⟨42, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))) else (if k <
    1069976994 then (if k < 1051462086 then (if k < 1049639910 then (if k = 1049638578 then ⟨41,
    ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1050816768 then (if k =
    1049639910 then ⟨829, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1050816768
    then ⟨318, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k <
    1051463418 then (if k = 1051462086 then ⟨828, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k < 1069762822 then (if k = 1051463418 then ⟨40, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 1069762822 then ⟨220, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 1098935188 then (if k < 1088058916 then (if k =
    1069976994 then ⟨349, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    < 1092486782 then (if k = 1088058916 then ⟨847, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k = 1092486782 then ⟨659, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1107575854 then (if k < 1105567404 then (if k = 1098935188
    then ⟨584, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1105567404
    then ⟨535, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 1112412819
    then (if k = 1107575854 then ⟨279, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k = 1112412819 then ⟨308, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩))))))))) else (if k < 1583424316 then (if k < 1369168292 then (if k < 1197415870
    then (if k < 1129946074 then (if k < 1126199158 then (if k < 1118933214 then (if k <
    1118286564 then (if k = 1116840685 then ⟨658, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 1118931882 then (if k = 1118286564 then ⟨317, ⟨[0, 1, 2], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1118931882 then ⟨39, ⟨[1, 0], [0],
    [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1119739209 then (if k = 1118933214 then
    ⟨827, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1125612954 then (if k =
    1119739209 then ⟨153, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    = 1125612954 then ⟨145, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else
    (if k < 1128073282 then (if k < 1126248442 then (if k = 1126199158 then ⟨28, ⟨[1, 0], [0],
    [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1128071950 then (if k = 1126248442 then ⟨26,
    ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1128071950 then ⟨30, ⟨[1, 0],
    [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1128122566 then (if k = 1128073282 then
    ⟨27, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1129407018 then (if k =
    1128122566 then ⟨25, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1129407018
    then ⟨366, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))) else (if k <
    1155694274 then (if k < 1144818002 then (if k < 1137446790 then (if k = 1129946074 then ⟨29,
    ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1142809552 then (if k =
    1137446790 then ⟨347, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    = 1142809552 then ⟨545, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if
    k < 1148217401 then (if k = 1144818002 then ⟨276, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k < 1153760921 then (if k = 1148217401 then ⟨641, ⟨[0, 1], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1153760921 then ⟨852, ⟨[0, 1, 2],
    [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 1173037200 then (if k <
    1167163455 then (if k = 1155694274 then ⟨855, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 1169171905 then (if k = 1167163455 then ⟨544, ⟨[1, 0], [0, 1],
    [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1169171905 then ⟨839, ⟨[0, 1, 2], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1185459549 then (if k <
    1175045650 then (if k = 1173037200 then ⟨536, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩) else (if k = 1175045650 then ⟨278, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩)) else (if k < 1195541746 then (if k = 1185459549 then ⟨631, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1195541746 then ⟨24, ⟨[1, 0], [0],
    [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))))) else (if k < 1273220304 then (if k < 1226807651 then
    (if k < 1209813452 then (if k < 1203737308 then (if k = 1197415870 then ⟨23, ⟨[1, 0], [0],
    [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1204297863 then (if k = 1203737308 then ⟨327,
    ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1204297863 then
    ⟨313, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1215687197
    then (if k = 1209813452 then ⟨630, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k < 1216791115 then (if k = 1215687197 then ⟨639, ⟨[0, 1], [0, 1], [false, false]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1216791115 then ⟨581, ⟨[0, 1], [0, 1], [false, false]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 1251161554 then (if k < 1236142491 then (if k =
    1226807651 then ⟨622, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k <
    1241145018 then (if k = 1236142491 then ⟨360, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 1241145018 then ⟨578, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩))) else (if k < 1260496394 then (if k < 1259048499 then (if k = 1251161554
    then ⟨624, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1259048499
    then ⟨542, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 1271767659
    then (if k = 1260496394 then ⟨358, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k = 1271767659 then ⟨314, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩))))) else (if k < 1326518295 then (if k < 1302070072 then (if k < 1282888113 then
    (if k = 1273220304 then ⟨168, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k < 1301698496 then (if k = 1282888113 then ⟨365, ⟨[0, 1, 2], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1301698496 then ⟨635, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1307242016 then (if k = 1302070072 then
    ⟨830, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1307943817
    then (if k = 1307242016 then ⟨850, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k = 1307943817 then ⟨59, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩)))) else (if k < 1343046598 then (if k < 1332864500 then (if k = 1326518295 then ⟨541,
    ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1338618732 then (if k
    = 1332864500 then ⟨291, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if
    k = 1338618732 then ⟨284, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))
    else (if k < 1357218403 then (if k < 1351111984 then (if k = 1343046598 then ⟨628, ⟨[0, 1],
    [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1351111984 then ⟨549, ⟨[0, 1],
    [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 1365105348 then (if k =
    1357218403 then ⟨294, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    = 1365105348 then ⟨160, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))))))
    else (if k < 1481568604 then (if k < 1412224684 then (if k < 1398792081 then (if k <
    1383187270 then (if k < 1375465887 then (if k = 1369168292 then ⟨637, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1380288746 then (if k = 1375465887
    then ⟨856, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1380288746
    then ⟨618, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k <
    1388595119 then (if k = 1383187270 then ⟨170, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 1389623586 then (if k = 1388595119 then ⟨372, ⟨[2, 1, 0], [1,
    0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1389623586 then ⟨339, ⟨[0, 1, 2],
    [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 1407541173 then (if k <
    1404642649 then (if k = 1398792081 then ⟨48, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 1406088528 then (if k = 1404642649 then ⟨620, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1406088528 then ⟨283, ⟨[0, 1, 2], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1410516394 then (if k =
    1407541173 then ⟨173, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    < 1410591845 then (if k = 1410516394 then ⟨627, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 1410591845 then ⟨593, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩))))) else (if k < 1447833993 then (if k < 1413977489 then (if k < 1412226016
    then (if k = 1412224684 then ⟨818, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    < 1413414918 then (if k = 1412226016 then ⟨9, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k = 1413414918 then ⟨141, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩))) else (if k < 1429943221 then (if k = 1413977489 then ⟨337, ⟨[0, 1, 2], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1436019365 then (if k = 1429943221
    then ⟨340, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k =
    1436019365 then ⟨601, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if
    k < 1467350931 then (if k < 1455551167 then (if k = 1447833993 then ⟨583, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1467185369 then (if k = 1455551167
    then ⟨832, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k =
    1467185369 then ⟨316, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else
    (if k < 1478061641 then (if k < 1472187896 then (if k = 1467350931 then ⟨551, ⟨[0, 1], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1472187896 then ⟨582, ⟨[0, 1], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 1481567272 then (if k =
    1478061641 then ⟨592, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k =
    1481567272 then ⟨817, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))))) else (if k <
    1526665230 then (if k < 1499426217 then (if k < 1492581464 then (if k < 1490707340 then (if
    k = 1481568604 then ⟨8, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k <
    1491539272 then (if k = 1490707340 then ⟨3, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k = 1491539272 then ⟨315, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩))) else (if k < 1497413017 then (if k = 1492581464 then ⟨2, ⟨[1, 0], [0], [true]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k < 1498865662 then (if k = 1497413017 then ⟨343, ⟨[2, 1, 0],
    [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1498865662 then ⟨144, ⟨[2, 1,
    0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 1510699498 then (if k <
    1503489161 then (if k = 1499426217 then ⟨156, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 1504593079 then (if k = 1503489161 then ⟨600, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1504593079 then ⟨548, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1521936005 then (if k < 1521257381
    then (if k = 1510699498 then ⟨348, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k = 1521257381 then ⟨130, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩)) else (if k < 1523944455 then (if k = 1521936005 then ⟨534, ⟨[1, 0], [0, 1],
    [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1523944455 then ⟨281, ⟨[0, 1, 2], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))) else (if k < 1547436211 then (if k <
    1534820727 then (if k < 1528275985 then (if k = 1526665230 then ⟨323, ⟨[2, 1, 0], [1, 0],
    [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1528946982 then (if k = 1528275985 then
    ⟨100, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1528946982
    then ⟨854, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k <
    1545611284 then (if k = 1534820727 then ⟨550, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 1546289908 then (if k = 1545611284 then ⟨132, ⟨[1, 2, 0], [1,
    0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1546289908 then ⟨533, ⟨[1, 0], [0,
    1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 1558177136 then (if k <
    1548298358 then (if k = 1547436211 then ⟨66, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 1554172103 then (if k = 1548298358 then ⟨280, ⟨[0, 1, 2], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1554172103 then ⟨344, ⟨[0, 1, 2],
    [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1564072940 then (if k <
    1560051260 then (if k = 1558177136 then ⟨1, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k = 1560051260 then ⟨0, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k
    < 1564586002 then (if k = 1564072940 then ⟨588, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 1564586002 then ⟨640, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩)))))))) else (if k < 1911867827 then (if k < 1771817197 then (if k <
    1680824949 then (if k < 1633747086 then (if k < 1618658014 then (if k < 1588939905 then (if
    k = 1583424316 then ⟨322, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else
    (if k < 1609546010 then (if k = 1588939905 then ⟨638, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k = 1609546010 then ⟨375, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1620666464 then (if k = 1618658014 then ⟨501, ⟨[1,
    0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1631542736 then (if k =
    1620666464 then ⟨312, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if
    k = 1631542736 then ⟨589, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else
    (if k < 1645020367 then (if k < 1640183402 then (if k = 1633747086 then ⟨275, ⟨[1, 2, 0],
    [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1643011917 then (if k =
    1640183402 then ⟨323, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if
    k = 1643011917 then ⟨500, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else
    (if k < 1650894112 then (if k = 1645020367 then ⟨311, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1675417100 then (if k = 1650894112 then ⟨321, ⟨[0, 1,
    2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1675417100 then ⟨540, ⟨[1,
    0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))) else (if k < 1736905411 then (if k <
    1701216882 then (if k < 1698393809 then (if k = 1680824949 then ⟨644, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1699771003 then (if k = 1698393809
    then ⟨556, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1699771003
    then ⟨539, ⟨[1, 0], [0, 1], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k <
    1717745185 then (if k = 1701216882 then ⟨274, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 1718067097 then (if k = 1717745185 then ⟨290, ⟨[0, 1, 2], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1718067097 then ⟨636, ⟨[0, 1], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 1748294745 then (if k <
    1742421000 then (if k = 1736905411 then ⟨340, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 1747616121 then (if k = 1742421000 then ⟨634, ⟨[0, 1], [0, 1],
    [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1747616121 then ⟨344, ⟨[2, 1, 0], [1,
    0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1759415199 then (if k < 1749226876
    then (if k = 1748294745 then ⟨643, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k = 1749226876 then ⟨104, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩)) else (if k < 1765863605 then (if k = 1759415199 then ⟨626, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1765863605 then ⟨555, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))))) else (if k < 1846311822 then (if k < 1804375207 then
    (if k < 1785214981 then (if k < 1779341236 then (if k = 1771817197 then ⟨228, ⟨[2, 1, 0],
    [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1783769102 then (if k =
    1779341236 then ⟨282, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if
    k = 1783769102 then ⟨629, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else
    (if k < 1786667626 then (if k = 1785214981 then ⟨288, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1792541371 then (if k = 1786667626 then ⟨140, ⟨[1, 2,
    0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1792541371 then ⟨147, ⟨[1,
    2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 1815145818 then (if k
    < 1804963720 then (if k = 1804375207 then ⟨343, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k < 1805827852 then (if k = 1804963720 then ⟨371, ⟨[2, 1, 0],
    [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1805827852 then ⟨159, ⟨[2, 1,
    0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1829317623 then (if k <
    1826960446 then (if k = 1815145818 then ⟨609, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 1826960446 then ⟨591, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩)) else (if k < 1839286993 then (if k = 1829317623 then ⟨373, ⟨[2, 1, 0], [1,
    0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1839286993 then ⟨227, ⟨[2, 1, 0],
    [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))) else (if k < 1871226280 then (if k <
    1859035732 then (if k < 1851314349 then (if k = 1846311822 then ⟨342, ⟨[2, 1, 0], [1, 0],
    [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1852387966 then (if k = 1851314349 then
    ⟨590, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1852387966 then
    ⟨599, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1869217830
    then (if k = 1859035732 then ⟨135, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k < 1870665725 then (if k = 1869217830 then ⟨526, ⟨[1, 0], [0, 1], [false,
    true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1870665725 then ⟨341, ⟨[2, 1, 0], [1, 0],
    [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 1883389635 then (if k < 1876741869
    then (if k = 1871226280 then ⟨285, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k < 1882615614 then (if k = 1876741869 then ⟨598, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1882615614 then ⟨606, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1903070908 then (if k < 1883719532 then (if
    k = 1883389635 then ⟨138, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else
    (if k = 1883719532 then ⟨553, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))
    else (if k < 1908073435 then (if k = 1903070908 then ⟨346, ⟨[0, 1, 2], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1908073435 then ⟨552, ⟨[0, 1], [0, 1], [false,
    false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))))) else (if k < 2055523536 then (if k < 1979337623 then
    (if k < 1943033831 then (if k < 1936687626 then (if k < 1921202667 then (if k = 1911867827
    then ⟨649, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1927424811
    then (if k = 1921202667 then ⟨369, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k = 1927424811 then ⟨345, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[],
    [], []⟩⟩))) else (if k < 1938696076 then (if k = 1936687626 then ⟨525, ⟨[1, 0], [0, 1],
    [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1940148721 then (if k = 1938696076 then
    ⟨287, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1940148721
    then ⟨155, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k <
    1958444815 then (if k < 1943199393 then (if k = 1943033831 then ⟨325, ⟨[2, 1, 0], [1, 0],
    [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1944644586 then (if k = 1943199393 then
    ⟨597, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1944644586 then
    ⟨99, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 1968626913
    then (if k < 1967387734 then (if k = 1958444815 then ⟨374, ⟨[2, 1, 0], [1, 0], [true,
    true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1967387734 then ⟨324, ⟨[2, 1, 0], [1, 0],
    [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 1968998489 then (if k = 1968626913 then
    ⟨602, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 1968998489 then
    ⟨98, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))) else (if k < 2010669189
    then (if k < 1988672463 then (if k < 1980441541 then (if k = 1979337623 then ⟨648, ⟨[0, 1],
    [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 1982798718 then (if k =
    1980441541 then ⟨587, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k =
    1982798718 then ⟨376, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if
    k < 1999792917 then (if k = 1988672463 then ⟨368, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k < 2004795444 then (if k = 1999792917 then ⟨320, ⟨[0, 1, 2],
    [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 2004795444 then ⟨586, ⟨[0, 1],
    [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 2032033765 then (if k <
    2012873539 then (if k = 2010669189 then ⟨596, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k < 2024146820 then (if k = 2012873539 then ⟨250, ⟨[1, 2, 0], [1,
    0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 2024146820 then ⟨319, ⟨[0, 1, 2],
    [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if k < 2041366595 then (if k <
    2036096709 then (if k = 2032033765 then ⟨162, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩) else (if k = 2036096709 then ⟨605, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0,
    ⟨[], [], []⟩⟩)) else (if k < 2050115687 then (if k = 2041366595 then ⟨55, ⟨[2, 1, 0], [1,
    0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 2050115687 then ⟨273, ⟨[1, 2, 0],
    [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))))) else (if k < 2096514926 then (if k <
    2068934339 then (if k < 2068834439 then (if k < 2056552003 then (if k = 2055523536 then
    ⟨303, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 2065720498
    then (if k = 2056552003 then ⟨325, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩) else (if k = 2065720498 then ⟨54, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [],
    []⟩⟩))) else (if k < 2068883723 then (if k = 2068834439 then ⟨36, ⟨[1, 0], [0], [true]⟩⟩
    else ⟨0, ⟨[], [], []⟩⟩) else (if k < 2068885055 then (if k = 2068883723 then ⟨38, ⟨[1, 0],
    [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 2068885055 then ⟨826, ⟨[1, 0], [0],
    [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else (if k < 2074469590 then (if k < 2070707231 then (if
    k = 2068934339 then ⟨37, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k <
    2070757847 then (if k = 2070707231 then ⟨825, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)
    else (if k = 2070757847 then ⟨35, ⟨[1, 0], [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))) else (if
    k < 2080343335 then (if k < 2077520262 then (if k = 2074469590 then ⟨272, ⟨[1, 2, 0], [1,
    0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 2077520262 then ⟨564, ⟨[0, 1], [0,
    1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 2080905906 then (if k =
    2080343335 then ⟨251, ⟨[1, 2, 0], [1, 0], [false, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    = 2080905906 then ⟨324, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))))
    else (if k < 2122479584 then (if k < 2098125681 then (if k < 2096871638 then (if k =
    2096514926 then ⟨346, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    < 2097193550 then (if k = 2096871638 then ⟨349, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩) else (if k = 2097193550 then ⟨645, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else
    ⟨0, ⟨[], [], []⟩⟩))) else (if k < 2120868829 then (if k = 2098125681 then ⟨103, ⟨[2, 1, 0],
    [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 2121547453 then (if k =
    2120868829 then ⟨345, ⟨[2, 1, 0], [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k
    = 2121547453 then ⟨642, ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))) else
    (if k < 2138177027 then (if k < 2122993332 then (if k = 2122479584 then ⟨102, ⟨[2, 1, 0],
    [1, 0], [true, true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k < 2134113786 then (if k =
    2122993332 then ⟨301, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if
    k = 2134113786 then ⟨844, ⟨[0, 1, 2], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)))
    else (if k < 2139116313 then (if k < 2138227643 then (if k = 2138177027 then ⟨34, ⟨[1, 0],
    [0], [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 2138227643 then ⟨824, ⟨[1, 0], [0],
    [true]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩)) else (if k < 2144990058 then (if k = 2139116313 then ⟨554,
    ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩) else (if k = 2144990058 then ⟨562,
    ⟨[0, 1], [0, 1], [false, false]⟩⟩ else ⟨0, ⟨[], [], []⟩⟩))))))))))

/-- A proposed finite column, used only together with its coverage proof. -/
def columnIndex (G : DecoratedStableGraph (Fin 4)) : Fin 860 := (lookupKey (graphKey G)).1

/-- Proposed ordered bijections for the same candidate. -/
def hint (G : DecoratedStableGraph (Fin 4)) : GraphIsomorphismHint :=
  (lookupKey (graphKey G)).2

end AxiomaticGW.L24InitialHints
