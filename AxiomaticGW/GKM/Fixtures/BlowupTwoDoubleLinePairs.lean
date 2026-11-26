/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoPositivePlaneEnergyTwoPairs
public import AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalPairs
public import AxiomaticGW.GKM.Fixtures.StrictLineCoverTransport

/-! # Native comparison of the 100 ordered pairs on twice the strict line

On the two ends of the strict-line edge, the hyperplane and both exceptional restrictions
have coefficient −1 on the exceptional class of F₁. The native lifts also have unit shifts.
Here the signed projection is checked directly on the final dimension-matched coefficients.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoDoubleLinePairs
open EquivariantCoefficients

/-- The first hundred rows of the positive-plane report retain the full curve class 2L. -/
def index (j : Fin 100) : Fin 300 := j.castLE (by decide)

/-- The ordered two-marked Bl₂ query and both versions of its native value. -/
abbrev requests (j : Fin 100) := BlowupTwoPositivePlaneEnergyTwoPairs.requests (index j)
abbrev values (j : Fin 100) := BlowupTwoPositivePlaneEnergyTwoPairs.values (index j)
noncomputable abbrev equivariant (j : Fin 100) :=
  BlowupTwoPositivePlaneEnergyTwoPairs.equivariant (index j)

/-- Under the ordinary signed restriction the three Bl₂ divisors all use the F₁ exceptional
insertion. The negative sign is accumulated separately for the entire ordered tuple. -/
def projectLabel : SurfaceBasisLabel .blowupTwo → SurfaceBasisLabel .hirzebruchOne
  | .unit => .unit
  | .point => .point
  | .hyperplane | .exceptional _ => .exceptional 0

/-- The F₁ comparison preserves the genus, both marking orders and all cotangent powers. -/
def project (q : SurfaceQuery .blowupTwo) : SurfaceQuery .hirzebruchOne :=
  ⟨q.genus, ![2, 0], q.insertions.map (fun s ↦ ⟨projectLabel s.label, s.psi⟩)⟩

/-- One negative sign for every divisor insertion. -/
def sign (q : SurfaceQuery .blowupTwo) : ℚ :=
  (-1 : ℚ) ^ q.insertions.countP (fun s ↦ s.label.codimension == 1)

/-- The exact row of the incoming F₁ report is determined by the projected full query. -/
def sourceRow? (q : SurfaceQuery .blowupTwo) : Option (Fin 64) :=
  (List.finRange 64).find? (fun k ↦ F1DoubleExceptionalPairs.requests k == project q)

/-- Every signed projection has a genuine row in the complete F₁ report. -/
theorem source_exists : ∀ j : Fin 100, (sourceRow? (requests j)).isSome := by
  decide +kernel

/-- Corresponding row of the complete doubled-exceptional F₁ report. -/
def sourceRow (j : Fin 100) : Fin 64 := (sourceRow? (requests j)).get (source_exists j)

/-- The signed comparison preserves the literal projected query on all 100 rows.
The F₁ packet has 36 distinct rows after the three Bl₂ divisors are identified. -/
theorem projection :
    (Finset.univ.image sourceRow).card = 36 ∧ ∀ j,
      (requests j).beta = ![0, 0, 2] ∧ F1DoubleExceptionalPairs.requests (sourceRow j) =
        project (requests j) ∧ values j = sign (requests j) * F1DoubleExceptionalPairs.values
          (sourceRow j) := by
  decide +kernel

/-- The two complete native fractions agree with the divisor sign after the strict-line torus
character change. This is a finite check on the full fractions in these two reports. -/
theorem field_comparison (j : Fin 100) :
    equivariant j = (sign (requests j) : Coefficient) *
      StrictLineCoverTransport.field (F1DoubleExceptionalPairs.equivariant (sourceRow j)) := by
  unfold equivariant
  rw [BlowupTwoPositivePlaneEnergyTwoPairs.equivariant_eq_ordinary,
    F1DoubleExceptionalPairs.equivariant_eq_ordinary, map_ratCast,
    show BlowupTwoPositivePlaneEnergyTwoPairs.values (index j) =
      sign (requests j) * F1DoubleExceptionalPairs.values (sourceRow j) from (projection.2 j).2.2,
    Rat.cast_mul]

end AxiomaticGW.GKM.BlowupTwoDoubleLinePairs
