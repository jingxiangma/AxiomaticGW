/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.SmallQuantumGeneratorComparison
public import AxiomaticGW.GKM.Fixtures.SurfaceFrames

/-!
# Small quantum multiplication to first ordinary Novikov order on all three surfaces

The coefficients are indexed by the individual effective generators. In the
quotient by the square of the positive-curve ideal these are all of the
nonconstant monomials. Every coefficientwise associativity check uses the
two ordered splittings of that particular generator and the actual surface
cup product.
-/

@[expose] public section
namespace AxiomaticGW.GKM.OrdinarySmallQuantumGenerators
open SmallQuantumGeneratorComparison

abbrev Index (X : SurfaceTarget) := Fin (X.blowups + 3)

/-- The last basis slot is the point, dual to the first slot (the unit). -/
def dualSlot (X : SurfaceTarget) (i : Index X) : Index X :=
  if i = 0 then Fin.last _ else if i = Fin.last _ then 0 else i

theorem dualSlot_correct (X : SurfaceTarget) : ∀ i, state X (dualSlot X i) = (state X i).dual := by
  cases X <;> decide +kernel

/-- The ordinary cup product from the established surface algebra. -/
noncomputable def classical : (X : SurfaceTarget) → Index X → Index X → Index X → ℚ
  | .plane => SurfaceFrames.Plane.request.ordinaryProducts
  | .hirzebruchOne => SurfaceFrames.OneBlowup.request.ordinaryProducts
  | .blowupTwo => SurfaceFrames.TwoBlowups.request.ordinaryProducts

/-- Raise the third entry of the whole native tensor with the ordinary inverse metric. -/
def coefficient (X : SurfaceTarget) (d : Fin (X.blowups + 1)) (i j k : Index X) : ℚ :=
  (state X k).inverseWeight * tensor (0 : ℚ) 0 X d i j (dualSlot X k)

/-- Pairing recovers every original reconstructed three-point invariant. -/
theorem pairing (X : SurfaceTarget) : ∀ d i j k,
    (state X k).inverseWeight * coefficient X d i j (dualSlot X k) =
      SurfaceGenusZero.primaryValue X (generator X d) {state X i, state X j, state X k} := by
  intro d i j k
  rw [← ordinary_replay]
  have h (X : SurfaceTarget) : ∀ d i j k,
      (state X k).inverseWeight * coefficient X d i j (dualSlot X k) =
        tensor (0 : ℚ) 0 X d i j k := by cases X <;> decide +kernel
  exact h X d i j k

theorem positive_unit (X : SurfaceTarget) : ∀ d j k, coefficient X d 0 j k = 0 := by
  cases X <;> decide +kernel

theorem commutative (X : SurfaceTarget) : ∀ d i j k,
    coefficient X d i j k = coefficient X d j i k := by cases X <;> decide +kernel

theorem ordered_splittings (X : SurfaceTarget) : ∀ d,
    X.splittings (generator X d) = {(0, generator X d), (generator X d, 0)} := by
  cases X <;> decide +kernel

/-- The first coefficient of the associative law with all intermediate surface basis states. -/
theorem associative (X : SurfaceTarget) : ∀ (d : Fin (X.blowups + 1)) (i j k l : Index X),
    (∑ h : Index X, (classical X i j h * coefficient X d h k l +
      coefficient X d i j h * classical X h k l)) =
    ∑ h : Index X, (classical X j k h * coefficient X d i h l +
      coefficient X d j k h * classical X i h l) := by
  cases X <;> decide +kernel

end AxiomaticGW.GKM.OrdinarySmallQuantumGenerators
