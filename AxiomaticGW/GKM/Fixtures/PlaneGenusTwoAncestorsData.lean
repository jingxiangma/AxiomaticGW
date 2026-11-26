/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoAncestorCache
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsData

/-!
# Complete candidate ancestor data for the plane few-marking suite

Input SHA256: 640e00ec2d4b2055c49465d80a3590da42dec51772d34ea00bad356dad0950a8
Candidate values become certificates only after their full equations are checked.
The original canonical seeds and geometric hypotheses are unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoAncestors

open BelorousskiPandharipande SurfaceGenusTwo

/-- Every full ancestor key, including degree-zero and vanishing rows. -/
def key (i : Fin 39) : SurfaceAncestorKey .plane :=
  (#[⟨2, ![0], ([⟨.point, 0⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![0], ([⟨.hyperplane, 0⟩, ⟨.point, 0⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![0], ([⟨.hyperplane, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![0], ([⟨.unit, 0⟩, ⟨.point, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![0], ([⟨.unit, 1⟩, ⟨.point, 0⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![0], ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![0], ([⟨.unit, 2⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![0], ([⟨.unit, 0⟩, ⟨.hyperplane, 2⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![0], ([⟨.unit, 1⟩, ⟨.hyperplane, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![0], ([⟨.unit, 2⟩, ⟨.hyperplane, 0⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.point, 0⟩, ⟨.point, 2⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.point, 1⟩, ⟨.point, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.point, 3⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![0], ([⟨.unit, 0⟩, ⟨.unit, 3⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![0], ([⟨.unit, 1⟩, ⟨.unit, 2⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.hyperplane, 0⟩, ⟨.point, 3⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.hyperplane, 1⟩, ⟨.point, 2⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.hyperplane, 2⟩, ⟨.point, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.hyperplane, 3⟩, ⟨.point, 0⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.hyperplane, 4⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 0⟩, ⟨.point, 4⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 1⟩, ⟨.point, 3⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 2⟩, ⟨.point, 2⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 3⟩, ⟨.point, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 4⟩, ⟨.point, 0⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 4⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.hyperplane, 1⟩, ⟨.hyperplane, 3⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.hyperplane, 2⟩, ⟨.hyperplane, 2⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 5⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 0⟩, ⟨.hyperplane, 5⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 1⟩, ⟨.hyperplane, 4⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 2⟩, ⟨.hyperplane, 3⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 3⟩, ⟨.hyperplane, 2⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 4⟩, ⟨.hyperplane, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 5⟩, ⟨.hyperplane, 0⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 0⟩, ⟨.unit, 6⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 1⟩, ⟨.unit, 5⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 2⟩, ⟨.unit, 4⟩] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨2, ![1], ([⟨.unit, 3⟩, ⟨.unit, 3⟩] : List (SurfaceInsertion .plane)), by decide⟩
    ] : Array (SurfaceAncestorKey .plane))[i.val]

/-- Exact candidate values, interpreted only after table acceptance. -/
def value (i : Fin 39) : ℚ :=
  (#[0,
    0,
    (-1 / 960),
    0,
    0,
    0,
    (7 / 640),
    (-1 / 960),
    (-1 / 320),
    (-1 / 960),
    (1 / 240),
    (1 / 144),
    (-9 / 640),
    (7 / 640),
    (21 / 640),
    (-1 / 320),
    (-1 / 960),
    (-1 / 192),
    (-7 / 960),
    (1 / 128),
    (-9 / 640),
    (-27 / 640),
    (-101 / 1920),
    (-67 / 1920),
    (-17 / 1920),
    (-1 / 160),
    (-13 / 480),
    (-31 / 960),
    0,
    (1 / 128),
    (3 / 128),
    (29 / 640),
    (29 / 640),
    (3 / 128),
    (1 / 128),
    0,
    0,
    0,
    0] : Array ℚ)[i.val]

/-- Complete original candidate boundary terms for row 0. -/
def terms_0 : RationalTerms (SurfaceAncestorKey .plane) :=
  0

/-- Complete original candidate boundary terms for row 1. -/
def terms_1 : RationalTerms (SurfaceAncestorKey .plane) :=
  0

/-- Complete original candidate boundary terms for row 2. -/
def terms_2 : RationalTerms (SurfaceAncestorKey .plane) :=
  0

/-- Complete original candidate boundary terms for row 3. -/
def terms_3 : RationalTerms (SurfaceAncestorKey .plane) :=
  0

/-- Complete original candidate boundary terms for row 4. -/
def terms_4 : RationalTerms (SurfaceAncestorKey .plane) :=
  0

/-- Complete original candidate boundary terms for row 5. -/
def terms_5 : RationalTerms (SurfaceAncestorKey .plane) :=
  0

/-- Complete original candidate boundary terms for row 6. -/
def terms_6 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((155 / 22464), 0),
    ((23 / 24960), 0),
    ((35 / 11232), 0)}

/-- Complete original candidate boundary terms for row 7. -/
def terms_7 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 2})}

/-- Complete original candidate boundary terms for row 8. -/
def terms_8 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (3, {key 2})}

/-- Complete original candidate boundary terms for row 9. -/
def terms_9 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 2})}

/-- Complete original candidate boundary terms for row 10. -/
def terms_10 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-3 / 8320), 0),
    ((-31 / 16848), 0),
    ((-7 / 33696), 0),
    (1, {key 2}),
    ((1 / 56160), 0),
    ((155 / 33696), 0),
    ((23 / 24960), 0),
    ((35 / 16848), 0)}

/-- Complete original candidate boundary terms for row 11. -/
def terms_11 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-161 / 8640), 0),
    ((-161 / 8640), 0),
    ((-37 / 5760), 0),
    ((-7 / 432), 0),
    ((1 / 720), 0),
    ((13 / 1920), 0),
    (3, {key 2}),
    ((5 / 108), 0),
    ((67 / 8640), 0),
    ((67 / 8640), 0)}

/-- Complete original candidate boundary terms for row 12. -/
def terms_12 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-155 / 22464), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-31 / 16848), 0),
    ((-31 / 16848), 0),
    ((-35 / 11232), 0),
    ((-7 / 16848), 0),
    ((-7 / 16848), 0),
    ((-7 / 33696), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((41 / 23868), 0)}

/-- Complete original candidate boundary terms for row 13. -/
def terms_13 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-35 / 11232), 0),
    ((-41 / 15912), 0),
    ((155 / 22464), 0),
    ((23 / 24960), 0),
    ((35 / 5616), 0),
    ((41 / 15912), 0)}

/-- Complete original candidate boundary terms for row 14. -/
def terms_14 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((155 / 11232), 0),
    ((155 / 22464), 0),
    ((23 / 24960), 0),
    ((23 / 24960), 0),
    ((23 / 24960), 0),
    ((35 / 11232), 0),
    ((35 / 5616), 0)}

/-- Complete original candidate boundary terms for row 15. -/
def terms_15 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-31 / 16848), 0),
    ((-31 / 16848), 0),
    ((-35 / 16848), 0),
    ((-41 / 23868), 0),
    ((-7 / 11232), 0),
    ((-7 / 16848), 0),
    ((-7 / 16848), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((23 / 24960), 0),
    ((35 / 16848), 0),
    ((41 / 23868), 0),
    ((41 / 23868), 0),
    ((7 / 33696), 0),
    ((7 / 33696), 0)}

/-- Complete original candidate boundary terms for row 16. -/
def terms_16 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-3 / 4160), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-31 / 8424), 0),
    ((-31 / 8424), 0),
    ((-31 / 8424), 0),
    ((-7 / 11232), 0),
    ((-7 / 11232), 0),
    ((-7 / 16848), 0),
    ((-749 / 168480), 0),
    ((1 / 18720), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((155 / 33696), 0),
    ((155 / 33696), 0),
    ((23 / 24960), 0),
    ((23 / 24960), 0),
    ((23 / 24960), 0),
    ((35 / 16848), 0),
    ((35 / 16848), 0),
    ((41 / 23868), 0)}

/-- Complete original candidate boundary terms for row 17. -/
def terms_17 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-31 / 8424), 0),
    ((-31 / 8424), 0),
    ((-31 / 8424), 0),
    ((-7 / 11232), 0),
    ((-7 / 16848), 0),
    ((-7 / 16848), 0),
    ((-749 / 168480), 0),
    ((-749 / 168480), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((155 / 33696), 0),
    ((155 / 33696), 0),
    ((23 / 24960), 0),
    ((23 / 37440), 0),
    ((23 / 37440), 0),
    ((35 / 16848), 0),
    ((35 / 16848), 0),
    ((41 / 23868), 0)}

/-- Complete original candidate boundary terms for row 18. -/
def terms_18 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-101 / 3818880), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-155 / 67392), 0),
    ((-3 / 4160), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-31 / 16848), 0),
    ((-31 / 16848), 0),
    ((-31 / 33696), 0),
    ((-35 / 11232), 0),
    ((-41 / 23868), 0),
    ((-7 / 11232), 0),
    ((-7 / 11232), 0),
    ((-7 / 16848), 0),
    ((1 / 18720), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((23 / 24960), 0),
    ((35 / 16848), 0),
    ((41 / 15912), 0),
    ((41 / 23868), 0),
    ((7 / 33696), 0)}

/-- Complete original candidate boundary terms for row 19. -/
def terms_19 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-41 / 15912), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((31 / 11232), 0),
    ((31 / 11232), 0),
    ((31 / 11232), 0),
    ((7 / 11232), 0),
    ((7 / 11232), 0),
    ((7 / 11232), 0)}

/-- Complete original candidate boundary terms for row 20. -/
def terms_20 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-155 / 22464), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-31 / 16848), 0),
    ((-31 / 16848), 0),
    ((-35 / 5616), 0),
    ((-41 / 15912), 0),
    ((-7 / 11232), 0),
    ((-7 / 11232), 0),
    ((-7 / 33696), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((35 / 11232), 0),
    ((41 / 15912), 0),
    ((41 / 23868), 0),
    ((7 / 33696), 0),
    ((7 / 33696), 0)}

/-- Complete original candidate boundary terms for row 21. -/
def terms_21 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-101 / 2864160), 0),
    ((-101 / 2864160), 0),
    ((-101 / 2864160), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-155 / 11232), 0),
    ((-155 / 22464), 0),
    ((-3 / 4160), 0),
    ((-3 / 4160), 0),
    ((-3 / 4160), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-31 / 5616), 0),
    ((-31 / 5616), 0),
    ((-35 / 11232), 0),
    ((-35 / 5616), 0),
    ((-7 / 11232), 0),
    ((-7 / 5616), 0),
    ((-7 / 5616), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((41 / 11934), 0),
    ((41 / 23868), 0)}

/-- Complete original candidate boundary terms for row 22. -/
def terms_22 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-155 / 11232), 0),
    ((-155 / 22464), 0),
    ((-23 / 24960), 0),
    ((-23 / 24960), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-31 / 5616), 0),
    ((-31 / 5616), 0),
    ((-35 / 11232), 0),
    ((-35 / 5616), 0),
    ((-7 / 11232), 0),
    ((-7 / 11232), 0),
    ((-7 / 33696), 0),
    ((-749 / 168480), 0),
    ((-749 / 168480), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((41 / 23868), 0)}

/-- Complete original candidate boundary terms for row 23. -/
def terms_23 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-1 / 4160), 0),
    ((-1 / 4160), 0),
    ((-1 / 4160), 0),
    ((-101 / 2864160), 0),
    ((-101 / 2864160), 0),
    ((-101 / 2864160), 0),
    ((-101 / 3818880), 0),
    ((-101 / 3818880), 0),
    ((-101 / 3818880), 0),
    ((-155 / 11232), 0),
    ((-155 / 33696), 0),
    ((-155 / 33696), 0),
    ((-155 / 33696), 0),
    ((-3 / 4160), 0),
    ((-3 / 4160), 0),
    ((-3 / 4160), 0),
    ((-35 / 16848), 0),
    ((-35 / 5616), 0),
    ((-7 / 11232), 0),
    ((-7 / 5616), 0),
    ((-7 / 5616), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((31 / 33696), 0),
    ((41 / 11934), 0),
    ((41 / 15912), 0)}

/-- Complete original candidate boundary terms for row 24. -/
def terms_24 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-101 / 11456640), 0),
    ((-101 / 11456640), 0),
    ((-101 / 11456640), 0),
    ((-155 / 22464), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-31 / 33696), 0),
    ((-31 / 33696), 0),
    ((-35 / 5616), 0),
    ((-35 / 67392), 0),
    ((-41 / 15912), 0),
    ((-7 / 22464), 0),
    ((1 / 18720), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((101 / 3818880), 0),
    ((31 / 8424), 0),
    ((35 / 11232), 0),
    ((41 / 23868), 0),
    ((41 / 47736), 0),
    ((7 / 22464), 0),
    ((7 / 22464), 0),
    ((7 / 22464), 0),
    ((7 / 67392), 0)}

/-- Complete original candidate boundary terms for row 25. -/
def terms_25 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-155 / 22464), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-35 / 5616), 0),
    ((-41 / 15912), 0),
    ((-41 / 47736), 0),
    ((-7 / 67392), 0),
    ((-7 / 67392), 0),
    ((-7 / 67392), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((101 / 11456640), 0),
    ((101 / 11456640), 0),
    ((101 / 11456640), 0),
    ((31 / 11232), 0),
    ((31 / 33696), 0),
    ((31 / 33696), 0),
    ((35 / 11232), 0),
    ((35 / 67392), 0),
    ((41 / 15912), 0),
    ((7 / 22464), 0),
    ((7 / 22464), 0)}

/-- Complete original candidate boundary terms for row 26. -/
def terms_26 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-101 / 3818880), 0),
    ((-101 / 3818880), 0),
    ((-101 / 3818880), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-101 / 5728320), 0),
    ((-155 / 11232), 0),
    ((-155 / 22464), 0),
    ((-3 / 4160), 0),
    ((-3 / 4160), 0),
    ((-3 / 4160), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-31 / 33696), 0),
    ((-31 / 33696), 0),
    ((-35 / 11232), 0),
    ((-35 / 5616), 0),
    ((-7 / 11232), 0),
    ((-7 / 11232), 0),
    ((1 / 14040), 0),
    ((1 / 14040), 0),
    ((1 / 14040), 0),
    ((1 / 14040), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 9360), 0),
    ((155 / 33696), 0),
    ((41 / 15912), 0),
    ((41 / 23868), 0)}

/-- Complete original candidate boundary terms for row 27. -/
def terms_27 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-155 / 11232), 0),
    ((-155 / 22464), 0),
    ((-23 / 24960), 0),
    ((-23 / 24960), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-3 / 8320), 0),
    ((-31 / 33696), 0),
    ((-31 / 33696), 0),
    ((-35 / 11232), 0),
    ((-35 / 5616), 0),
    ((-41 / 47736), 0),
    ((-7 / 67392), 0),
    ((-749 / 112320), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 28080), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((101 / 11456640), 0),
    ((101 / 11456640), 0),
    ((101 / 11456640), 0),
    ((155 / 33696), 0),
    ((35 / 67392), 0),
    ((7 / 22464), 0),
    ((749 / 336960), 0),
    ((749 / 336960), 0)}

/-- Complete original candidate boundary terms for row 28. -/
def terms_28 : RationalTerms (SurfaceAncestorKey .plane) :=
  0

/-- Complete original candidate boundary terms for row 29. -/
def terms_29 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-41 / 15912), 0),
    ((-7 / 22464), 0),
    ((-7 / 22464), 0),
    ((-7 / 22464), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((31 / 11232), 0),
    ((31 / 11232), 0),
    ((31 / 11232), 0),
    ((7 / 7488), 0),
    ((7 / 7488), 0),
    ((7 / 7488), 0)}

/-- Complete original candidate boundary terms for row 30. -/
def terms_30 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-41 / 15912), 0),
    ((-41 / 7956), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((101 / 1909440), 0),
    ((101 / 1909440), 0),
    ((101 / 1909440), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((31 / 3744), 0),
    ((31 / 3744), 0),
    ((31 / 3744), 0),
    ((7 / 3744), 0),
    ((7 / 3744), 0),
    ((7 / 3744), 0)}

/-- Complete original candidate boundary terms for row 31. -/
def terms_31 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-41 / 15912), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((31 / 3744), 0),
    ((31 / 3744), 0),
    ((31 / 3744), 0),
    ((7 / 7488), 0),
    ((7 / 7488), 0),
    ((7 / 7488), 0),
    ((749 / 112320), 0),
    ((749 / 112320), 0),
    ((749 / 112320), 0)}

/-- Complete original candidate boundary terms for row 32. -/
def terms_32 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-41 / 15912), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((31 / 3744), 0),
    ((31 / 3744), 0),
    ((31 / 3744), 0),
    ((7 / 7488), 0),
    ((7 / 7488), 0),
    ((7 / 7488), 0),
    ((749 / 112320), 0),
    ((749 / 112320), 0),
    ((749 / 112320), 0)}

/-- Complete original candidate boundary terms for row 33. -/
def terms_33 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-41 / 15912), 0),
    ((-41 / 7956), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((1 / 18720), 0),
    ((101 / 1909440), 0),
    ((101 / 1909440), 0),
    ((101 / 1909440), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((31 / 3744), 0),
    ((31 / 3744), 0),
    ((31 / 3744), 0),
    ((7 / 3744), 0),
    ((7 / 3744), 0),
    ((7 / 3744), 0)}

/-- Complete original candidate boundary terms for row 34. -/
def terms_34 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    ((-41 / 15912), 0),
    ((-7 / 22464), 0),
    ((-7 / 22464), 0),
    ((-7 / 22464), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((1 / 56160), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((101 / 3818880), 0),
    ((31 / 11232), 0),
    ((31 / 11232), 0),
    ((31 / 11232), 0),
    ((7 / 7488), 0),
    ((7 / 7488), 0),
    ((7 / 7488), 0)}

/-- Complete original candidate boundary terms for row 35. -/
def terms_35 : RationalTerms (SurfaceAncestorKey .plane) :=
  0

/-- Complete original candidate boundary terms for row 36. -/
def terms_36 : RationalTerms (SurfaceAncestorKey .plane) :=
  0

/-- Complete original candidate boundary terms for row 37. -/
def terms_37 : RationalTerms (SurfaceAncestorKey .plane) :=
  0

/-- Complete original candidate boundary terms for row 38. -/
def terms_38 : RationalTerms (SurfaceAncestorKey .plane) :=
  0

/-- All original terms, preserving coefficients and repeated occurrences. -/
def terms (i : Fin 39) : RationalTerms (SurfaceAncestorKey .plane) :=
  (#[terms_0,
    terms_1,
    terms_2,
    terms_3,
    terms_4,
    terms_5,
    terms_6,
    terms_7,
    terms_8,
    terms_9,
    terms_10,
    terms_11,
    terms_12,
    terms_13,
    terms_14,
    terms_15,
    terms_16,
    terms_17,
    terms_18,
    terms_19,
    terms_20,
    terms_21,
    terms_22,
    terms_23,
    terms_24,
    terms_25,
    terms_26,
    terms_27,
    terms_28,
    terms_29,
    terms_30,
    terms_31,
    terms_32,
    terms_33,
    terms_34,
    terms_35,
    terms_36,
    terms_37,
    terms_38] : Array (RationalTerms (SurfaceAncestorKey .plane)))[i.val]

/-- The finite cache keeps complete keys; equal energy does not merge queries. -/
def queries : Finset (SurfaceAncestorKey .plane) := Finset.univ.image key

/-- Candidate lookup; callers must check membership and table acceptance. -/
def values (q : SurfaceAncestorKey .plane) : ℚ :=
  (((List.finRange 39).find? (fun i ↦ key i = q)).map value).getD 0

/-- No two rows denote the same full ancestor. -/
theorem keys_injective : Function.Injective key := by decide +kernel

/-- Every declared row is returned by the lookup. -/
theorem values_key : ∀ i, values (key i) = value i := by decide +kernel

end AxiomaticGW.GKM.PlaneGenusTwoAncestors
