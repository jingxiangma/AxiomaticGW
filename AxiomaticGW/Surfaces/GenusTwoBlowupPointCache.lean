/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoL24PointCache
public import AxiomaticGW.Surfaces.GenusTwoBlowupScalar
public import AxiomaticGW.Surfaces.GenusTwoPrimaryConstant

/-!
# Reusing certified primary point functions in the selected blowup constants

The H branch retains the complete L24 contraction with its proved higher-genus
guard. The P, N and K branches use the existing exact lower-genus BP shortcut.
Every source class, point count, exceptional label and N-row weight is unchanged.
Only the genus-zero and genus-one point backends are arguments. Their equality
to the existing evaluators proves equality to the actual selected scalar row.
This generic module imports no bounded table or numerical fixture.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupPointCache

open SurfaceGenusTwoBlowupOrder

variable {X : SurfaceTarget}

/-- The unchanged H/P/N/K constant dispatch with reusable primary point backends. -/
def constant (i : Fin X.blowups) (s : State X) (v₀ v₁ : X.Curve → ℚ) : ℚ :=
  match s.2 with
  | .hyperplane => L24Relation.pointConstantWithPoints X v₀ v₁
      (X.effective.energy s.1 - 1) (s.1 + X.exceptionalCurve i)
      ![.hyperplane, .exceptional i, .exceptional i, .exceptional i]
  | .point => BelorousskiPandharipande.lowerPointConstantWithPrimary X v₀ v₁
      (X.effective.energy s.1 - 1) s.1 ![.hyperplane, .hyperplane, .hyperplane]
  | .primary =>
      (3 * (X.planeDegree s.1 : ℚ) / 2) *
        BelorousskiPandharipande.lowerPointConstantWithPrimary X v₀ v₁
          (X.effective.energy s.1) (s.1 + X.exceptionalCurve i)
          ![.exceptional i, .hyperplane, .hyperplane] +
      (-1) * BelorousskiPandharipande.lowerPointConstantWithPrimary X v₀ v₁
        (X.effective.energy s.1) (s.1 + X.exceptionalCurve i)
        ![.exceptional i, .exceptional i, .hyperplane] +
      ((X.planeDegree s.1 : ℚ) / 2) *
        BelorousskiPandharipande.lowerPointConstantWithPrimary X v₀ v₁
          (X.effective.energy s.1) (s.1 + X.exceptionalCurve i)
          ![.exceptional i, .exceptional i, .exceptional i] +
      (-1 / 3) * BelorousskiPandharipande.lowerPointConstantWithPrimary X v₀ v₁
        (X.effective.energy s.1) (s.1 + X.exceptionalCurve i)
        ![.hyperplane, .hyperplane, .hyperplane]
  | .exceptional j => BelorousskiPandharipande.lowerPointConstantWithPrimary X v₀ v₁
      (X.effective.energy s.1 - 1) s.1 ![.exceptional j, .exceptional j, .exceptional j]

/-- Point-backend reuse preserves the actual scalar constant for every full state. -/
theorem constant_eq (i : Fin X.blowups) (s : State X) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X) :
    constant i s v₀ v₁ = SurfaceGenusTwoBlowupScalar.constant i s := by
  obtain ⟨beta, family⟩ := s
  cases family <;>
    simp only [constant, SurfaceGenusTwoBlowupScalar.constant,
      L24Relation.pointConstantWithPoints_eq X v₀ v₁ h₀ h₁,
      BelorousskiPandharipande.lowerPointConstantWithPrimary_eq X v₀ v₁ h₀ h₁]

end AxiomaticGW.SurfaceGenusTwoBlowupPointCache
