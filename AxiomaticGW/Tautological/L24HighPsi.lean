/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Graphs
public import AxiomaticGW.Tautological.StrataOperationReplay
public import AxiomaticGW.Tautological.Fixtures.GenusTwoPsiPullbacksReplay

/-!
# Actual genus-two high-power corrections in L24

Each context attaches an existing two- or three-marked psi relation to its
rational component. The source label carrying a cotangent power may become
a node. Destination hints are checked against the complete decorated graph.
-/

@[expose] public section

namespace AxiomaticGW.L24HighPsi
open RelationCertificate

set_option maxRecDepth 20000

open StrataOperation

/-- Attach the product source for upstream column 47; its last flag is the node. -/
def context47 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.refl _))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination47 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 50, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 56, 0, 0,
    108, 0, 121, 122, 0, 124, 0, 0, 0, 126, 127, 128, 129, 0, 0, 130, 131, 132, 0, 134, 0, 0,
    135, 0, 137, 138, 139, 377, 378, 379, 380, 381, 382, 383, 417, 418, 419, 420, 421, 422, 423,
    424, 425, 426, 0, 489, 0, 499, 500, 501, 0, 662, 663, 664, 665, 666, 667, 668, 669, 670,
    671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 805]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered47 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context47.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination47 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image47 :
    context47.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination47 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context47.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered47

/-- Attach the product source for upstream column 48; its last flag is the node. -/
def context48 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.mk ![0, 2, 1] ![0, 2, 1]
    (by decide +kernel) (by decide +kernel) )).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.refl _))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination48 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 48, 0, 0, 52, 0, 0, 0, 51, 0, 0, 0, 0, 0, 0, 56, 0, 0,
    107, 0, 121, 123, 0, 124, 0, 0, 0, 131, 132, 133, 134, 0, 0, 125, 126, 127, 0, 129, 0, 0,
    136, 0, 137, 138, 139, 377, 378, 381, 382, 379, 380, 383, 418, 417, 419, 420, 422, 421, 423,
    426, 425, 424, 0, 489, 0, 499, 500, 502, 0, 662, 664, 663, 665, 667, 666, 668, 669, 671,
    670, 672, 673, 675, 674, 676, 677, 679, 678, 680, 805]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered48 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context48.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination48 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image48 :
    context48.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination48 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context48.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered48

/-- Attach the square source for upstream column 49; its last flag is the node. -/
def context49 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.mk ![1, 0, 2] ![1, 0, 2]
    (by decide +kernel) (by decide +kernel) )).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.refl _))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination49 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 0, 0, 53, 0, 0, 0, 0, 0, 0, 56, 0, 0,
    108, 0, 122, 0, 0, 124, 0, 0, 0, 126, 128, 0, 129, 0, 0, 0, 139, 135, 0, 137, 0, 0, 0, 0,
    134, 130, 131, 0, 0, 377, 378, 381, 382, 383, 417, 420, 421, 418, 419, 422, 423, 425, 424,
    426, 0, 489, 0, 499, 501, 0, 0, 0, 662, 664, 665, 666, 669, 670, 667, 668, 671, 672, 673,
    674, 677, 678, 675, 676, 679, 680, 805]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered49 : ∀ i, GenusTwoPsiPullbacksReplay.squareThreeClaim i ≠ 0 →
    (context49.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination49 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image49 :
    context49.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination49 GenusTwoPsiPullbacksReplay.squareThreeClaim) :=
  context49.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered49

/-- Attach the product source for upstream column 50; its last flag is the node. -/
def context50 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.mk ![1, 2, 0] ![2, 0, 1]
    (by decide +kernel) (by decide +kernel) )).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.refl _))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination50 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 50, 0, 0, 52, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 56, 0, 0,
    106, 0, 122, 123, 0, 124, 0, 0, 0, 139, 135, 136, 137, 0, 0, 125, 126, 128, 0, 129, 0, 0,
    133, 0, 134, 130, 131, 379, 380, 381, 382, 377, 378, 383, 420, 417, 421, 418, 422, 419, 423,
    426, 424, 425, 0, 489, 0, 499, 501, 502, 0, 663, 664, 662, 665, 669, 666, 670, 667, 671,
    668, 672, 673, 677, 674, 678, 675, 679, 676, 680, 805]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered50 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context50.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination50 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image50 :
    context50.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination50 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context50.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered50

/-- Attach the square source for upstream column 57; its last flag is the node. -/
def context57 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![0, 2, 1, 3] ![0, 2, 1, 3]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination57 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 62, 0, 0, 0, 0, 0, 0, 63, 0, 0,
    111, 0, 140, 0, 0, 142, 0, 0, 0, 143, 144, 0, 146, 0, 0, 0, 148, 149, 0, 150, 0, 0, 0, 0,
    152, 153, 154, 0, 0, 386, 387, 388, 389, 390, 427, 428, 429, 430, 431, 432, 433, 434, 435,
    436, 0, 490, 0, 503, 504, 0, 0, 0, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692,
    693, 694, 695, 696, 697, 698, 699, 806]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered57 : ∀ i, GenusTwoPsiPullbacksReplay.squareThreeClaim i ≠ 0 →
    (context57.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination57 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image57 :
    context57.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination57 GenusTwoPsiPullbacksReplay.squareThreeClaim) :=
  context57.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered57

/-- Attach the product source for upstream column 58; its last flag is the node. -/
def context58 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![0, 2, 1, 3] ![0, 2, 1, 3]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination58 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 57, 0, 0, 59, 0, 0, 0, 62, 0, 0, 0, 0, 0, 0, 63, 0, 0,
    111, 0, 140, 141, 0, 142, 0, 0, 0, 143, 144, 145, 146, 0, 0, 147, 148, 149, 0, 150, 0, 0,
    151, 0, 152, 153, 154, 384, 385, 386, 387, 388, 389, 390, 427, 428, 429, 430, 431, 432, 433,
    434, 435, 436, 0, 490, 0, 503, 504, 505, 0, 681, 682, 683, 684, 685, 686, 687, 688, 689,
    690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 806]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered58 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context58.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination58 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image58 :
    context58.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination58 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context58.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered58

/-- Attach the square source for upstream column 60; its last flag is the node. -/
def context60 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.mk ![1, 0, 2] ![1, 0, 2]
    (by decide +kernel) (by decide +kernel) )).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![0, 2, 1, 3] ![0, 2, 1, 3]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination60 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 0, 0, 62, 0, 0, 0, 0, 0, 0, 63, 0, 0,
    111, 0, 141, 0, 0, 142, 0, 0, 0, 143, 145, 0, 146, 0, 0, 0, 154, 151, 0, 152, 0, 0, 0, 0,
    150, 147, 148, 0, 0, 384, 385, 388, 389, 390, 427, 430, 431, 428, 429, 432, 433, 435, 434,
    436, 0, 490, 0, 503, 505, 0, 0, 0, 681, 683, 684, 685, 688, 689, 686, 687, 690, 691, 692,
    693, 696, 697, 694, 695, 698, 699, 806]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered60 : ∀ i, GenusTwoPsiPullbacksReplay.squareThreeClaim i ≠ 0 →
    (context60.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination60 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image60 :
    context60.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination60 GenusTwoPsiPullbacksReplay.squareThreeClaim) :=
  context60.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered60

/-- Attach the square source for upstream column 68; its last flag is the node. -/
def context68 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![0, 3, 1, 2] ![0, 2, 3, 1]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination68 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 0, 0, 69, 0, 0, 0, 0, 0, 0, 70, 0, 0,
    114, 0, 155, 0, 0, 157, 0, 0, 0, 158, 159, 0, 161, 0, 0, 0, 163, 164, 0, 165, 0, 0, 0, 0,
    167, 168, 169, 0, 0, 393, 394, 395, 396, 397, 437, 438, 439, 440, 441, 442, 443, 444, 445,
    446, 0, 491, 0, 506, 507, 0, 0, 0, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711,
    712, 713, 714, 715, 716, 717, 718, 807]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered68 : ∀ i, GenusTwoPsiPullbacksReplay.squareThreeClaim i ≠ 0 →
    (context68.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination68 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image68 :
    context68.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination68 GenusTwoPsiPullbacksReplay.squareThreeClaim) :=
  context68.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered68

/-- Attach the product source for upstream column 69; its last flag is the node. -/
def context69 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![0, 3, 1, 2] ![0, 2, 3, 1]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination69 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 64, 0, 0, 66, 0, 0, 0, 69, 0, 0, 0, 0, 0, 0, 70, 0, 0,
    114, 0, 155, 156, 0, 157, 0, 0, 0, 158, 159, 160, 161, 0, 0, 162, 163, 164, 0, 165, 0, 0,
    166, 0, 167, 168, 169, 391, 392, 393, 394, 395, 396, 397, 437, 438, 439, 440, 441, 442, 443,
    444, 445, 446, 0, 491, 0, 506, 507, 508, 0, 700, 701, 702, 703, 704, 705, 706, 707, 708,
    709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 807]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered69 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context69.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination69 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image69 :
    context69.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination69 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context69.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered69

/-- Attach the square source for upstream column 71; its last flag is the node. -/
def context71 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.mk ![1, 0, 2] ![1, 0, 2]
    (by decide +kernel) (by decide +kernel) )).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![0, 3, 1, 2] ![0, 2, 3, 1]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination71 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, 69, 0, 0, 0, 0, 0, 0, 70, 0, 0,
    114, 0, 156, 0, 0, 157, 0, 0, 0, 158, 160, 0, 161, 0, 0, 0, 169, 166, 0, 167, 0, 0, 0, 0,
    165, 162, 163, 0, 0, 391, 392, 395, 396, 397, 437, 440, 441, 438, 439, 442, 443, 445, 444,
    446, 0, 491, 0, 506, 508, 0, 0, 0, 700, 702, 703, 704, 707, 708, 705, 706, 709, 710, 711,
    712, 715, 716, 713, 714, 717, 718, 807]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered71 : ∀ i, GenusTwoPsiPullbacksReplay.squareThreeClaim i ≠ 0 →
    (context71.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination71 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image71 :
    context71.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination71 GenusTwoPsiPullbacksReplay.squareThreeClaim) :=
  context71.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered71

/-- Attach the square source for upstream column 93; its last flag is the node. -/
def context93 : StrataOperation 2 (Fin 2) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 2) 2 (Fin 2)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 4) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 4) _ 0 0)
    (by norm_num [StableArity]) 1 3).relabel (Equiv.refl _))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination93 : Fin 38 → Fin 815 :=
  ![0, 0, 0, 0, 13, 0, 0, 0, 74, 0, 173, 0, 175, 0, 0, 0, 179, 180, 181, 398, 447, 448, 449, 0,
    492, 0, 509, 513, 0, 719, 720, 721, 722, 723, 724, 725, 726, 808]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered93 : ∀ i, GenusTwoPsiPullbacksReplay.squareTwoClaim i ≠ 0 →
    (context93.graph (GenusTwoPsiProduct.graph i)).isomorphic?
      (L24Graphs.graph (destination93 i)) = true := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image93 :
    context93.map
      (interpret GenusTwoPsiProduct.columns GenusTwoPsiPullbacksReplay.squareTwoClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination93 GenusTwoPsiPullbacksReplay.squareTwoClaim) :=
  context93.map_interpret _ GenusTwoPsiProduct.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered93

/-- Attach the product source for upstream column 94; its last flag is the node. -/
def context94 : StrataOperation 2 (Fin 2) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 2) 2 (Fin 2)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 4) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 4) _ 0 0)
    (by norm_num [StableArity]) 1 3).relabel (Equiv.refl _))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination94 : Fin 38 → Fin 815 :=
  ![0, 0, 0, 0, 0, 14, 0, 0, 74, 0, 173, 174, 175, 0, 0, 178, 179, 180, 181, 398, 447, 448, 449,
    0, 492, 0, 509, 513, 514, 719, 720, 721, 722, 723, 724, 725, 726, 808]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered94 : ∀ i, GenusTwoPsiProduct.requested i ≠ 0 →
    (context94.graph (GenusTwoPsiProduct.graph i)).isomorphic?
      (L24Graphs.graph (destination94 i)) = true := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image94 :
    context94.map
      (interpret GenusTwoPsiProduct.columns GenusTwoPsiProduct.requested) =
      interpret L24Graphs.columns
        (imageCoordinates destination94 GenusTwoPsiProduct.requested) :=
  context94.map_interpret _ GenusTwoPsiProduct.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered94

/-- Attach the square source for upstream column 101; its last flag is the node. -/
def context101 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![1, 2, 0, 3] ![2, 0, 1, 3]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination101 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 68, 0, 0, 0, 0, 0, 0, 81, 0, 0,
    114, 0, 182, 0, 0, 185, 0, 0, 0, 187, 188, 0, 190, 0, 0, 0, 192, 193, 0, 195, 0, 0, 0, 0,
    198, 199, 200, 0, 0, 401, 402, 395, 396, 403, 450, 451, 452, 453, 454, 455, 456, 457, 458,
    459, 0, 493, 0, 515, 516, 0, 0, 0, 728, 702, 729, 730, 731, 732, 733, 734, 735, 736, 737,
    738, 739, 740, 741, 742, 743, 744, 809]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered101 : ∀ i, GenusTwoPsiPullbacksReplay.squareThreeClaim i ≠ 0 →
    (context101.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination101 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image101 :
    context101.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination101 GenusTwoPsiPullbacksReplay.squareThreeClaim) :=
  context101.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered101

/-- Attach the product source for upstream column 102; its last flag is the node. -/
def context102 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![1, 2, 0, 3] ![2, 0, 1, 3]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination102 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 75, 0, 0, 77, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 81, 0, 0,
    114, 0, 182, 183, 0, 185, 0, 0, 0, 187, 188, 189, 190, 0, 0, 191, 192, 193, 0, 195, 0, 0,
    196, 0, 198, 199, 200, 399, 400, 401, 402, 395, 396, 403, 450, 451, 452, 453, 454, 455, 456,
    457, 458, 459, 0, 493, 0, 515, 516, 517, 0, 727, 728, 702, 729, 730, 731, 732, 733, 734,
    735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 809]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered102 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context102.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination102 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image102 :
    context102.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination102 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context102.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered102

/-- Attach the product source for upstream column 103; its last flag is the node. -/
def context103 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.mk ![0, 2, 1] ![0, 2, 1]
    (by decide +kernel) (by decide +kernel) )).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![1, 2, 0, 3] ![2, 0, 1, 3]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination103 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 75, 0, 0, 69, 0, 0, 0, 78, 0, 0, 0, 0, 0, 0, 81, 0, 0,
    116, 0, 182, 184, 0, 185, 0, 0, 0, 192, 193, 194, 195, 0, 0, 186, 187, 188, 0, 190, 0, 0,
    197, 0, 198, 199, 200, 399, 400, 395, 396, 401, 402, 403, 451, 450, 452, 453, 455, 454, 456,
    459, 458, 457, 0, 493, 0, 515, 516, 518, 0, 727, 702, 728, 729, 731, 730, 732, 733, 735,
    734, 736, 737, 739, 738, 740, 741, 743, 742, 744, 809]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered103 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context103.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination103 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image103 :
    context103.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination103 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context103.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered103

/-- Attach the product source for upstream column 105; its last flag is the node. -/
def context105 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.mk ![1, 2, 0] ![2, 0, 1]
    (by decide +kernel) (by decide +kernel) )).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![1, 2, 0, 3] ![2, 0, 1, 3]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination105 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 77, 0, 0, 69, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 81, 0, 0,
    115, 0, 183, 184, 0, 185, 0, 0, 0, 200, 196, 197, 198, 0, 0, 186, 187, 189, 0, 190, 0, 0,
    194, 0, 195, 191, 192, 401, 402, 395, 396, 399, 400, 403, 453, 450, 454, 451, 455, 452, 456,
    459, 457, 458, 0, 493, 0, 515, 517, 518, 0, 728, 702, 727, 729, 733, 730, 734, 731, 735,
    732, 736, 737, 741, 738, 742, 739, 743, 740, 744, 809]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered105 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context105.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination105 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image105 :
    context105.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination105 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context105.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered105

/-- Attach the square source for upstream column 112; its last flag is the node. -/
def context112 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![1, 3, 0, 2] ![2, 0, 3, 1]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination112 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 0, 0, 61, 0, 0, 0, 0, 0, 0, 88, 0, 0,
    111, 0, 201, 0, 0, 204, 0, 0, 0, 206, 207, 0, 209, 0, 0, 0, 211, 212, 0, 214, 0, 0, 0, 0,
    217, 218, 219, 0, 0, 406, 407, 388, 389, 408, 460, 461, 462, 463, 464, 465, 466, 467, 468,
    469, 0, 494, 0, 519, 520, 0, 0, 0, 746, 683, 747, 748, 749, 750, 751, 752, 753, 754, 755,
    756, 757, 758, 759, 760, 761, 762, 810]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered112 : ∀ i, GenusTwoPsiPullbacksReplay.squareThreeClaim i ≠ 0 →
    (context112.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination112 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image112 :
    context112.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination112 GenusTwoPsiPullbacksReplay.squareThreeClaim) :=
  context112.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered112

/-- Attach the product source for upstream column 113; its last flag is the node. -/
def context113 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![1, 3, 0, 2] ![2, 0, 3, 1]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination113 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 82, 0, 0, 84, 0, 0, 0, 61, 0, 0, 0, 0, 0, 0, 88, 0, 0,
    111, 0, 201, 202, 0, 204, 0, 0, 0, 206, 207, 208, 209, 0, 0, 210, 211, 212, 0, 214, 0, 0,
    215, 0, 217, 218, 219, 404, 405, 406, 407, 388, 389, 408, 460, 461, 462, 463, 464, 465, 466,
    467, 468, 469, 0, 494, 0, 519, 520, 521, 0, 745, 746, 683, 747, 748, 749, 750, 751, 752,
    753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 810]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered113 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context113.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination113 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image113 :
    context113.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination113 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context113.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered113

/-- Attach the product source for upstream column 114; its last flag is the node. -/
def context114 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.mk ![0, 2, 1] ![0, 2, 1]
    (by decide +kernel) (by decide +kernel) )).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![1, 3, 0, 2] ![2, 0, 3, 1]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination114 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 82, 0, 0, 62, 0, 0, 0, 85, 0, 0, 0, 0, 0, 0, 88, 0, 0,
    118, 0, 201, 203, 0, 204, 0, 0, 0, 211, 212, 213, 214, 0, 0, 205, 206, 207, 0, 209, 0, 0,
    216, 0, 217, 218, 219, 404, 405, 388, 389, 406, 407, 408, 461, 460, 462, 463, 465, 464, 466,
    469, 468, 467, 0, 494, 0, 519, 520, 522, 0, 745, 683, 746, 747, 749, 748, 750, 751, 753,
    752, 754, 755, 757, 756, 758, 759, 761, 760, 762, 810]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered114 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context114.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination114 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image114 :
    context114.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination114 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context114.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered114

/-- Attach the product source for upstream column 116; its last flag is the node. -/
def context116 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.mk ![1, 2, 0] ![2, 0, 1]
    (by decide +kernel) (by decide +kernel) )).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![1, 3, 0, 2] ![2, 0, 3, 1]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination116 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 0, 0, 84, 0, 0, 62, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 88, 0, 0,
    117, 0, 202, 203, 0, 204, 0, 0, 0, 219, 215, 216, 217, 0, 0, 205, 206, 208, 0, 209, 0, 0,
    213, 0, 214, 210, 211, 406, 407, 388, 389, 404, 405, 408, 463, 460, 464, 461, 465, 462, 466,
    469, 467, 468, 0, 494, 0, 519, 521, 522, 0, 746, 683, 745, 747, 751, 748, 752, 749, 753,
    750, 754, 755, 759, 756, 760, 757, 761, 758, 762, 810]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered116 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context116.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination116 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image116 :
    context116.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination116 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context116.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered116

/-- Attach the square source for upstream column 137; its last flag is the node. -/
def context137 : StrataOperation 2 (Fin 2) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 2) 2 (Fin 2)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 4) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 4) _ 0 0)
    (by norm_num [StableArity]) 1 3).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2, 3]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination137 : Fin 38 → Fin 815 :=
  ![0, 0, 0, 0, 29, 0, 0, 0, 92, 0, 223, 0, 225, 0, 0, 0, 230, 231, 232, 409, 470, 471, 472, 0,
    495, 0, 523, 527, 0, 763, 764, 765, 766, 767, 768, 769, 770, 811]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered137 : ∀ i, GenusTwoPsiPullbacksReplay.squareTwoClaim i ≠ 0 →
    (context137.graph (GenusTwoPsiProduct.graph i)).isomorphic?
      (L24Graphs.graph (destination137 i)) = true := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image137 :
    context137.map
      (interpret GenusTwoPsiProduct.columns GenusTwoPsiPullbacksReplay.squareTwoClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination137 GenusTwoPsiPullbacksReplay.squareTwoClaim) :=
  context137.map_interpret _ GenusTwoPsiProduct.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered137

/-- Attach the product source for upstream column 138; its last flag is the node. -/
def context138 : StrataOperation 2 (Fin 2) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 2) 2 (Fin 2)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 4) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 4) _ 0 0)
    (by norm_num [StableArity]) 1 3).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2, 3]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination138 : Fin 38 → Fin 815 :=
  ![0, 0, 0, 0, 0, 30, 0, 0, 92, 0, 223, 224, 225, 0, 0, 229, 230, 231, 232, 409, 470, 471, 472,
    0, 495, 0, 523, 527, 528, 763, 764, 765, 766, 767, 768, 769, 770, 811]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered138 : ∀ i, GenusTwoPsiProduct.requested i ≠ 0 →
    (context138.graph (GenusTwoPsiProduct.graph i)).isomorphic?
      (L24Graphs.graph (destination138 i)) = true := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image138 :
    context138.map
      (interpret GenusTwoPsiProduct.columns GenusTwoPsiProduct.requested) =
      interpret L24Graphs.columns
        (imageCoordinates destination138 GenusTwoPsiProduct.requested) :=
  context138.map_interpret _ GenusTwoPsiProduct.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered138

/-- Attach the square source for upstream column 145; its last flag is the node. -/
def context145 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![2, 3, 0, 1] ![2, 3, 0, 1]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination145 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 0, 0, 52, 0, 0, 0, 0, 0, 0, 97, 0, 0,
    108, 0, 233, 0, 0, 235, 0, 0, 0, 236, 237, 0, 239, 0, 0, 0, 241, 242, 0, 243, 0, 0, 0, 0,
    245, 246, 247, 0, 0, 412, 413, 381, 382, 414, 473, 474, 475, 476, 477, 478, 479, 480, 481,
    482, 0, 496, 0, 529, 530, 0, 0, 0, 772, 664, 773, 774, 775, 776, 777, 778, 779, 780, 781,
    782, 783, 784, 785, 786, 787, 788, 812]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered145 : ∀ i, GenusTwoPsiPullbacksReplay.squareThreeClaim i ≠ 0 →
    (context145.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination145 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image145 :
    context145.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination145 GenusTwoPsiPullbacksReplay.squareThreeClaim) :=
  context145.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered145

/-- Attach the product source for upstream column 146; its last flag is the node. -/
def context146 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![2, 3, 0, 1] ![2, 3, 0, 1]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination146 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 93, 0, 0, 95, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 97, 0, 0,
    108, 0, 233, 234, 0, 235, 0, 0, 0, 236, 237, 238, 239, 0, 0, 240, 241, 242, 0, 243, 0, 0,
    244, 0, 245, 246, 247, 410, 411, 412, 413, 381, 382, 414, 473, 474, 475, 476, 477, 478, 479,
    480, 481, 482, 0, 496, 0, 529, 530, 531, 0, 771, 772, 664, 773, 774, 775, 776, 777, 778,
    779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 812]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered146 : ∀ i, GenusTwoPsiPullbacksReplay.productThreeClaim i ≠ 0 →
    (context146.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination146 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image146 :
    context146.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination146 GenusTwoPsiPullbacksReplay.productThreeClaim) :=
  context146.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered146

/-- Attach the square source for upstream column 148; its last flag is the node. -/
def context148 : StrataOperation 2 (Fin 3) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 3) 2 (Fin 3)).relabel (Equiv.mk ![1, 0, 2] ![1, 0, 2]
    (by decide +kernel) (by decide +kernel) )).join
    (DecoratedStableGraph.oneVertex 0 (Fin 3) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 3) _ 0 0)
    (by norm_num [StableArity]) 2 2).relabel (Equiv.mk ![2, 3, 0, 1] ![2, 3, 0, 1]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination148 : Fin 100 → Fin 815 :=
  ![0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 0, 0, 52, 0, 0, 0, 0, 0, 0, 97, 0, 0,
    108, 0, 234, 0, 0, 235, 0, 0, 0, 236, 238, 0, 239, 0, 0, 0, 247, 244, 0, 245, 0, 0, 0, 0,
    243, 240, 241, 0, 0, 410, 411, 381, 382, 414, 473, 476, 477, 474, 475, 478, 479, 481, 480,
    482, 0, 496, 0, 529, 531, 0, 0, 0, 771, 664, 773, 774, 777, 778, 775, 776, 779, 780, 781,
    782, 785, 786, 783, 784, 787, 788, 812]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered148 : ∀ i, GenusTwoPsiPullbacksReplay.squareThreeClaim i ≠ 0 →
    (context148.graph (BelorousskiPandharipande.graph i)).isomorphic?
      (L24Graphs.graph (destination148 i)) = true := by
  simp only [BelorousskiPandharipande.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image148 :
    context148.map
      (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination148 GenusTwoPsiPullbacksReplay.squareThreeClaim) :=
  context148.map_interpret _ BelorousskiPandharipande.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered148

/-- Attach the square source for upstream column 170; its last flag is the node. -/
def context170 : StrataOperation 2 (Fin 2) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 2) 2 (Fin 2)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 4) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 4) _ 0 0)
    (by norm_num [StableArity]) 1 3).relabel (Equiv.mk ![2, 0, 1, 3] ![1, 2, 0, 3]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination170 : Fin 38 → Fin 815 :=
  ![0, 0, 0, 0, 37, 0, 0, 0, 101, 0, 251, 0, 253, 0, 0, 0, 257, 258, 259, 415, 483, 484, 485, 0,
    497, 0, 532, 536, 0, 789, 790, 791, 792, 793, 794, 795, 796, 813]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered170 : ∀ i, GenusTwoPsiPullbacksReplay.squareTwoClaim i ≠ 0 →
    (context170.graph (GenusTwoPsiProduct.graph i)).isomorphic?
      (L24Graphs.graph (destination170 i)) = true := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image170 :
    context170.map
      (interpret GenusTwoPsiProduct.columns GenusTwoPsiPullbacksReplay.squareTwoClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination170 GenusTwoPsiPullbacksReplay.squareTwoClaim) :=
  context170.map_interpret _ GenusTwoPsiProduct.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered170

/-- Attach the product source for upstream column 171; its last flag is the node. -/
def context171 : StrataOperation 2 (Fin 2) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 2) 2 (Fin 2)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 4) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 4) _ 0 0)
    (by norm_num [StableArity]) 1 3).relabel (Equiv.mk ![2, 0, 1, 3] ![1, 2, 0, 3]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination171 : Fin 38 → Fin 815 :=
  ![0, 0, 0, 0, 0, 38, 0, 0, 101, 0, 251, 252, 253, 0, 0, 256, 257, 258, 259, 415, 483, 484,
    485, 0, 497, 0, 532, 536, 537, 789, 790, 791, 792, 793, 794, 795, 796, 813]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered171 : ∀ i, GenusTwoPsiProduct.requested i ≠ 0 →
    (context171.graph (GenusTwoPsiProduct.graph i)).isomorphic?
      (L24Graphs.graph (destination171 i)) = true := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image171 :
    context171.map
      (interpret GenusTwoPsiProduct.columns GenusTwoPsiProduct.requested) =
      interpret L24Graphs.columns
        (imageCoordinates destination171 GenusTwoPsiProduct.requested) :=
  context171.map_interpret _ GenusTwoPsiProduct.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered171

/-- Attach the square source for upstream column 192; its last flag is the node. -/
def context192 : StrataOperation 2 (Fin 2) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 2) 2 (Fin 2)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 4) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 4) _ 0 0)
    (by norm_num [StableArity]) 1 3).relabel (Equiv.mk ![3, 0, 1, 2] ![1, 2, 3, 0]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination192 : Fin 38 → Fin 815 :=
  ![0, 0, 0, 0, 42, 0, 0, 0, 105, 0, 263, 0, 265, 0, 0, 0, 269, 270, 271, 416, 486, 487, 488, 0,
    498, 0, 538, 542, 0, 797, 798, 799, 800, 801, 802, 803, 804, 814]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered192 : ∀ i, GenusTwoPsiPullbacksReplay.squareTwoClaim i ≠ 0 →
    (context192.graph (GenusTwoPsiProduct.graph i)).isomorphic?
      (L24Graphs.graph (destination192 i)) = true := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image192 :
    context192.map
      (interpret GenusTwoPsiProduct.columns GenusTwoPsiPullbacksReplay.squareTwoClaim) =
      interpret L24Graphs.columns
        (imageCoordinates destination192 GenusTwoPsiPullbacksReplay.squareTwoClaim) :=
  context192.map_interpret _ GenusTwoPsiProduct.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered192

/-- Attach the product source for upstream column 193; its last flag is the node. -/
def context193 : StrataOperation 2 (Fin 2) 2 (Fin 4) :=
  ((((.input : StrataOperation 2 (Fin 2) 2 (Fin 2)).relabel (Equiv.refl _)).join
    (DecoratedStableGraph.oneVertex 0 (Fin 4) (by norm_num [StableArity]) 0 0)
    (DecoratedStableGraph.oneVertex_totalGenus 0 (Fin 4) _ 0 0)
    (by norm_num [StableArity]) 1 3).relabel (Equiv.mk ![3, 0, 1, 2] ![1, 2, 3, 0]
      (by decide +kernel) (by decide +kernel) ))

/-- Untrusted finite lookup; coverage below supplies its mathematical meaning. -/
def destination193 : Fin 38 → Fin 815 :=
  ![0, 0, 0, 0, 0, 43, 0, 0, 105, 0, 263, 264, 265, 0, 0, 268, 269, 270, 271, 416, 486, 487,
    488, 0, 498, 0, 538, 542, 543, 797, 798, 799, 800, 801, 802, 803, 804, 814]

/-- All nonzero source columns map to their actual decorated destinations. -/
theorem covered193 : ∀ i, GenusTwoPsiProduct.requested i ≠ 0 →
    (context193.graph (GenusTwoPsiProduct.graph i)).isomorphic?
      (L24Graphs.graph (destination193 i)) = true := by
  simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The entire contextual source, including every remainder term, is represented. -/
theorem image193 :
    context193.map
      (interpret GenusTwoPsiProduct.columns GenusTwoPsiProduct.requested) =
      interpret L24Graphs.columns
        (imageCoordinates destination193 GenusTwoPsiProduct.requested) :=
  context193.map_interpret _ GenusTwoPsiProduct.graph_totalGenus _ L24Graphs.graph_totalGenus
    _ _ covered193

/-- All 29 actual contextual source expressions in their retained reduction order. -/
noncomputable def corrections : Fin 29 → StrataModule 2 (Fin 4) :=
  ![context47.map (interpret BelorousskiPandharipande.columns
    GenusTwoPsiPullbacksReplay.productThreeClaim), context48.map (interpret
    BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim),
    context49.map (interpret BelorousskiPandharipande.columns
    GenusTwoPsiPullbacksReplay.squareThreeClaim), context50.map (interpret
    BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim),
    context57.map (interpret BelorousskiPandharipande.columns
    GenusTwoPsiPullbacksReplay.squareThreeClaim), context58.map (interpret
    BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim),
    context60.map (interpret BelorousskiPandharipande.columns
    GenusTwoPsiPullbacksReplay.squareThreeClaim), context68.map (interpret
    BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim), context69.map
    (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim),
    context71.map (interpret BelorousskiPandharipande.columns
    GenusTwoPsiPullbacksReplay.squareThreeClaim), context93.map (interpret
    GenusTwoPsiProduct.columns GenusTwoPsiPullbacksReplay.squareTwoClaim), context94.map
    (interpret GenusTwoPsiProduct.columns GenusTwoPsiProduct.requested), context101.map
    (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim),
    context102.map (interpret BelorousskiPandharipande.columns
    GenusTwoPsiPullbacksReplay.productThreeClaim), context103.map (interpret
    BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim),
    context105.map (interpret BelorousskiPandharipande.columns
    GenusTwoPsiPullbacksReplay.productThreeClaim), context112.map (interpret
    BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim),
    context113.map (interpret BelorousskiPandharipande.columns
    GenusTwoPsiPullbacksReplay.productThreeClaim), context114.map (interpret
    BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.productThreeClaim),
    context116.map (interpret BelorousskiPandharipande.columns
    GenusTwoPsiPullbacksReplay.productThreeClaim), context137.map (interpret
    GenusTwoPsiProduct.columns GenusTwoPsiPullbacksReplay.squareTwoClaim), context138.map
    (interpret GenusTwoPsiProduct.columns GenusTwoPsiProduct.requested), context145.map
    (interpret BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim),
    context146.map (interpret BelorousskiPandharipande.columns
    GenusTwoPsiPullbacksReplay.productThreeClaim), context148.map (interpret
    BelorousskiPandharipande.columns GenusTwoPsiPullbacksReplay.squareThreeClaim),
    context170.map (interpret GenusTwoPsiProduct.columns
    GenusTwoPsiPullbacksReplay.squareTwoClaim), context171.map (interpret
    GenusTwoPsiProduct.columns GenusTwoPsiProduct.requested), context192.map (interpret
    GenusTwoPsiProduct.columns GenusTwoPsiPullbacksReplay.squareTwoClaim), context193.map
    (interpret GenusTwoPsiProduct.columns GenusTwoPsiProduct.requested)]

/-- Coordinates computed from the source coefficients and checked graph destinations. -/
def correctionCoordinates : Fin 29 → Coordinates 815 :=
  ![imageCoordinates destination47 GenusTwoPsiPullbacksReplay.productThreeClaim,
    imageCoordinates destination48 GenusTwoPsiPullbacksReplay.productThreeClaim,
    imageCoordinates destination49 GenusTwoPsiPullbacksReplay.squareThreeClaim, imageCoordinates
    destination50 GenusTwoPsiPullbacksReplay.productThreeClaim, imageCoordinates destination57
    GenusTwoPsiPullbacksReplay.squareThreeClaim, imageCoordinates destination58
    GenusTwoPsiPullbacksReplay.productThreeClaim, imageCoordinates destination60
    GenusTwoPsiPullbacksReplay.squareThreeClaim, imageCoordinates destination68
    GenusTwoPsiPullbacksReplay.squareThreeClaim, imageCoordinates destination69
    GenusTwoPsiPullbacksReplay.productThreeClaim, imageCoordinates destination71
    GenusTwoPsiPullbacksReplay.squareThreeClaim, imageCoordinates destination93
    GenusTwoPsiPullbacksReplay.squareTwoClaim, imageCoordinates destination94
    GenusTwoPsiProduct.requested, imageCoordinates destination101
    GenusTwoPsiPullbacksReplay.squareThreeClaim, imageCoordinates destination102
    GenusTwoPsiPullbacksReplay.productThreeClaim, imageCoordinates destination103
    GenusTwoPsiPullbacksReplay.productThreeClaim, imageCoordinates destination105
    GenusTwoPsiPullbacksReplay.productThreeClaim, imageCoordinates destination112
    GenusTwoPsiPullbacksReplay.squareThreeClaim, imageCoordinates destination113
    GenusTwoPsiPullbacksReplay.productThreeClaim, imageCoordinates destination114
    GenusTwoPsiPullbacksReplay.productThreeClaim, imageCoordinates destination116
    GenusTwoPsiPullbacksReplay.productThreeClaim, imageCoordinates destination137
    GenusTwoPsiPullbacksReplay.squareTwoClaim, imageCoordinates destination138
    GenusTwoPsiProduct.requested, imageCoordinates destination145
    GenusTwoPsiPullbacksReplay.squareThreeClaim, imageCoordinates destination146
    GenusTwoPsiPullbacksReplay.productThreeClaim, imageCoordinates destination148
    GenusTwoPsiPullbacksReplay.squareThreeClaim, imageCoordinates destination170
    GenusTwoPsiPullbacksReplay.squareTwoClaim, imageCoordinates destination171
    GenusTwoPsiProduct.requested, imageCoordinates destination192
    GenusTwoPsiPullbacksReplay.squareTwoClaim, imageCoordinates destination193
    GenusTwoPsiProduct.requested]

/-- The complete finite family is connected to its actual source operations. -/
theorem corrections_eq_interpret (i : Fin 29) :
    corrections i = interpret L24Graphs.columns (correctionCoordinates i) := by
  fin_cases i
  · exact image47
  · exact image48
  · exact image49
  · exact image50
  · exact image57
  · exact image58
  · exact image60
  · exact image68
  · exact image69
  · exact image71
  · exact image93
  · exact image94
  · exact image101
  · exact image102
  · exact image103
  · exact image105
  · exact image112
  · exact image113
  · exact image114
  · exact image116
  · exact image137
  · exact image138
  · exact image145
  · exact image146
  · exact image148
  · exact image170
  · exact image171
  · exact image192
  · exact image193

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- The primitive compatibility conditions for precisely these 29 contexts. -/
def Compatible (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (P : PsiClasses C) : Prop :=
  ∀ i : Fin 29,
    (![context47.Compatible A F P (by norm_num [StableArity]) , context48.Compatible A F P
      (by norm_num [StableArity]) , context49.Compatible A F P (by norm_num [StableArity]) ,
      context50.Compatible A F P (by norm_num [StableArity]) , context57.Compatible A F P
      (by norm_num [StableArity]) , context58.Compatible A F P (by norm_num [StableArity]) ,
      context60.Compatible A F P (by norm_num [StableArity]) , context68.Compatible A F P
      (by norm_num [StableArity]) , context69.Compatible A F P (by norm_num [StableArity]) ,
      context71.Compatible A F P (by norm_num [StableArity]) , context93.Compatible A F P
      (by norm_num [StableArity]) , context94.Compatible A F P (by norm_num [StableArity]) ,
      context101.Compatible A F P (by norm_num [StableArity]) , context102.Compatible A F P
      (by norm_num [StableArity]) , context103.Compatible A F P (by norm_num [StableArity]) ,
      context105.Compatible A F P (by norm_num [StableArity]) , context112.Compatible A F P
      (by norm_num [StableArity]) , context113.Compatible A F P (by norm_num [StableArity]) ,
      context114.Compatible A F P (by norm_num [StableArity]) , context116.Compatible A F P
      (by norm_num [StableArity]) , context137.Compatible A F P (by norm_num [StableArity]) ,
      context138.Compatible A F P (by norm_num [StableArity]) , context145.Compatible A F P
      (by norm_num [StableArity]) , context146.Compatible A F P (by norm_num [StableArity]) ,
      context148.Compatible A F P (by norm_num [StableArity]) , context170.Compatible A F P
      (by norm_num [StableArity]) , context171.Compatible A F P (by norm_num [StableArity]) ,
      context192.Compatible A F P (by norm_num [StableArity]) , context193.Compatible A F P
      (by norm_num [StableArity]) ]) i

/-- Four already constructed source relations suffice for all 29 corrections. -/
theorem corrections_vanish
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (P : PsiClasses C) (hc : Compatible A F P)
    (hs2 : (A 2 (Fin 2)).map GenusTwoPsiPullbacks.squareTwo.strata = 0)
    (hs3 : (A 2 (Fin 3)).map GenusTwoPsiPullbacks.squareThree.strata = 0)
    (hp2 : (A 2 (Fin 2)).map GenusTwoPsiProduct.cotangentRelation.strata = 0)
    (hp3 : (A 2 (Fin 3)).map GenusTwoPsiPullbacks.productThree.strata = 0)
    (i : Fin 29) : (A 2 (Fin 4)).map (corrections i) = 0 := by
  rw [GenusTwoPsiPullbacksReplay.squareTwo_strata] at hs2
  rw [GenusTwoPsiPullbacksReplay.squareThree_strata] at hs3
  rw [GenusTwoPsiProduct.cotangentRelation_strata] at hp2
  rw [GenusTwoPsiPullbacksReplay.productThree_strata] at hp3
  fin_cases i
  · exact context47.map_vanishes A F P _ (hc 0) _ hp3
  · exact context48.map_vanishes A F P _ (hc 1) _ hp3
  · exact context49.map_vanishes A F P _ (hc 2) _ hs3
  · exact context50.map_vanishes A F P _ (hc 3) _ hp3
  · exact context57.map_vanishes A F P _ (hc 4) _ hs3
  · exact context58.map_vanishes A F P _ (hc 5) _ hp3
  · exact context60.map_vanishes A F P _ (hc 6) _ hs3
  · exact context68.map_vanishes A F P _ (hc 7) _ hs3
  · exact context69.map_vanishes A F P _ (hc 8) _ hp3
  · exact context71.map_vanishes A F P _ (hc 9) _ hs3
  · exact context93.map_vanishes A F P _ (hc 10) _ hs2
  · exact context94.map_vanishes A F P _ (hc 11) _ hp2
  · exact context101.map_vanishes A F P _ (hc 12) _ hs3
  · exact context102.map_vanishes A F P _ (hc 13) _ hp3
  · exact context103.map_vanishes A F P _ (hc 14) _ hp3
  · exact context105.map_vanishes A F P _ (hc 15) _ hp3
  · exact context112.map_vanishes A F P _ (hc 16) _ hs3
  · exact context113.map_vanishes A F P _ (hc 17) _ hp3
  · exact context114.map_vanishes A F P _ (hc 18) _ hp3
  · exact context116.map_vanishes A F P _ (hc 19) _ hp3
  · exact context137.map_vanishes A F P _ (hc 20) _ hs2
  · exact context138.map_vanishes A F P _ (hc 21) _ hp2
  · exact context145.map_vanishes A F P _ (hc 22) _ hs3
  · exact context146.map_vanishes A F P _ (hc 23) _ hp3
  · exact context148.map_vanishes A F P _ (hc 24) _ hs3
  · exact context170.map_vanishes A F P _ (hc 25) _ hs2
  · exact context171.map_vanishes A F P _ (hc 26) _ hp2
  · exact context192.map_vanishes A F P _ (hc 27) _ hs2
  · exact context193.map_vanishes A F P _ (hc 28) _ hp2

end AxiomaticGW.L24HighPsi
