/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPrimaryConstant
public import AxiomaticGW.Surfaces.PlaneGenusTwoInitial
public import AxiomaticGW.Surfaces.Fixtures.PlaneGenusOneSupport

/-!
# Plane BP constants using certified lower-genus point values

The certified primary tables extend through energy fifteen: the quartic
genus-two equations use source degree five. Outside that range the original
algorithms remain the specification and fallback. Thus the shortcut neither
truncates an internal query nor turns an uncertified number into a seed.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo

/-- Reuse the proved rational table only inside its complete energy bound. -/
def planeRationalPointValue (beta : SurfaceTarget.plane.Curve) : ℚ :=
  if SurfaceTarget.plane.effective.energy beta ≤ 15 then PlaneGenusZeroSupport.values beta
  else SurfaceGenusZero.pointValue .plane beta

theorem planeRationalPointValue_eq :
    planeRationalPointValue = SurfaceGenusZero.pointValue .plane := by
  funext beta
  unfold planeRationalPointValue
  split_ifs with hb
  · exact PlaneGenusZeroSupport.values_eq beta hb
  · rfl

/-- Reuse the proved elliptic table, including its certified zero entries. -/
def planeEllipticPointValue (beta : SurfaceTarget.plane.Curve) : ℚ :=
  if SurfaceTarget.plane.effective.energy beta ≤ 15 then PlaneGenusOneSupport.values beta
  else SurfaceGenusOne.pointValue .plane beta

theorem planeEllipticPointValue_eq :
    planeEllipticPointValue = SurfaceGenusOne.pointValue .plane := by
  funext beta
  unfold planeEllipticPointValue
  split_ifs with hb
  · exact PlaneGenusOneSupport.values_eq beta hb
  · rfl

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.BelorousskiPandharipande
open SurfaceGenusTwo

/-- One complete diagram contribution, retaining all six marking occurrences.
Separate replay of these terms bounds kernel-checking memory. -/
def planePointConstantDiagram (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) (i : Fin 16) : ℚ :=
  rawPaperCoefficient (Fin.natAdd 4 i) * ∑ e,
    let z := orbitCotangentTerm (Fin.natAdd 4 i) e
    SurfaceGenusOne.primaryGraphDimensionEval .plane
      planeRationalPointValue planeEllipticPointValue z.expression beta n a

/-- The exact scalar BP constant, reusing already verified primary computations. -/
def planePointConstant (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) : ℚ :=
  ∑ i, planePointConstantDiagram n beta a i

/-- This is equality with the complete normalized polynomial at every degree. -/
theorem planePointConstant_eq (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) :
    planePointConstant n beta a = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (normalizedGenusTwoTerms .plane n beta 0 (SurfaceGenusZero.pointLabels a n)) := by
  have h : planePointConstant n beta a =
      lowerPointConstantWithPrimary .plane planeRationalPointValue planeEllipticPointValue
        n beta a := by
    unfold planePointConstant lowerPointConstantWithPrimary
    apply Finset.sum_congr rfl
    intro i _
    unfold planePointConstantDiagram
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    dsimp only
    have hg : (orbitCotangentTerm (Fin.natAdd 4 i) e).expression.maxComponentGenus ≤ 1 :=
      paperTerm_lower_genus (Fin.natAdd 4 i) (by change 4 ≤ 4 + i.val; omega)
    rw [SurfaceGenusOne.primaryGraphDimensionEval_eq,
      primaryGraphEval_pointContraction_eq .plane _ _
        (orbitCotangentTerm (Fin.natAdd 4 i) e).expression hg
        (orbitCotangentTerm (Fin.natAdd 4 i) e).labels,
      GluingExpression.scalarPointContraction_eq, lowerTerm_decoration_zero]
  rw [h, lowerPointConstantWithPrimary_eq .plane _ _
    planeRationalPointValue_eq planeEllipticPointValue_eq, pointConstant_plane_eq]

/-- The three complete shifted constants, with their original marking counts. -/
def planeShiftedConstantFast (d : ℕ) : Fin 3 → ℚ :=
  ![planePointConstant (3 * d + 1) ![d + 1] ![.hyperplane, .hyperplane, .point],
    planePointConstant (3 * d) ![d + 1] ![.hyperplane, .point, .point],
    planePointConstant (3 * d - 1) ![d + 1] ![.point, .point, .point]]

/-- No constant or full class is lost, including at degree zero. -/
theorem planeShiftedConstantFast_eq (d : ℕ) (i : Fin 3) :
    planeShiftedConstantFast d i = planeShiftedConstant d i := by
  fin_cases i <;> exact planePointConstant_eq _ _ _

end AxiomaticGW.BelorousskiPandharipande
