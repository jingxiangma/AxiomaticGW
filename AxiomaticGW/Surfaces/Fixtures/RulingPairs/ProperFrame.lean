/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Frame
public import AxiomaticGW.Surfaces.GenusTwoPairTerms

/-! # Proper-class ancestor keys in the two-marked ruling calibration

Each class is given in full effective coordinates. The two symbols for exceptional
insertions distinguish the component of the reducible ruling fiber from the
other exceptional divisor. The 68 proper keys consist of 26 low-power, 12
first-power product and 30 square profiles.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingInterior
open BlowupTwoRuling (X label)
open SurfaceGenusTwo

/-- Proper class, then relative label and power for both marking occurrences. -/
def properProfile (r : Fin 68) : Fin 3 × (Fin 5 × ℕ) × (Fin 5 × ℕ) :=
  (#[(0, (0, 0), (4, 1)), (0, (0, 0), (1, 2)), (0, (0, 0), (2, 2)),
    (0, (0, 0), (3, 2)), (0, (0, 0), (0, 3)), (0, (1, 0), (4, 0)),
    (0, (1, 0), (1, 1)), (0, (1, 0), (2, 1)), (0, (1, 0), (3, 1)),
    (0, (1, 0), (0, 2)), (0, (2, 0), (4, 0)), (0, (2, 0), (1, 1)),
    (0, (2, 0), (2, 1)), (0, (2, 0), (3, 1)), (0, (2, 0), (0, 2)),
    (0, (3, 0), (4, 0)), (0, (3, 0), (1, 1)), (0, (3, 0), (2, 1)),
    (0, (3, 0), (3, 1)), (0, (3, 0), (0, 2)), (0, (4, 0), (0, 1)),
    (0, (0, 1), (1, 1)), (0, (0, 1), (2, 1)), (0, (0, 1), (3, 1)),
    (0, (0, 1), (0, 2)), (1, (1, 0), (4, 1)), (1, (1, 0), (1, 2)),
    (1, (1, 0), (2, 2)), (1, (1, 0), (3, 2)), (1, (1, 0), (0, 3)),
    (1, (2, 0), (4, 1)), (1, (2, 0), (1, 2)), (1, (2, 0), (2, 2)),
    (1, (2, 0), (3, 2)), (1, (2, 0), (0, 3)), (1, (3, 0), (4, 1)),
    (1, (3, 0), (1, 2)), (1, (3, 0), (2, 2)), (1, (3, 0), (3, 2)),
    (1, (3, 0), (0, 3)), (1, (4, 0), (4, 0)), (1, (4, 0), (1, 1)),
    (1, (4, 0), (2, 1)), (1, (4, 0), (3, 1)), (1, (4, 0), (0, 2)),
    (1, (1, 1), (1, 1)), (1, (1, 1), (2, 1)), (1, (1, 1), (3, 1)),
    (1, (1, 1), (0, 2)), (1, (2, 1), (2, 1)), (1, (2, 1), (3, 1)),
    (1, (2, 1), (0, 2)), (1, (3, 1), (3, 1)), (1, (3, 1), (0, 2)),
    (2, (2, 0), (4, 1)), (2, (2, 0), (1, 2)), (2, (2, 0), (2, 2)),
    (2, (2, 0), (3, 2)), (2, (2, 0), (0, 3)), (2, (4, 0), (4, 0)),
    (2, (4, 0), (1, 1)), (2, (4, 0), (2, 1)), (2, (4, 0), (3, 1)),
    (2, (4, 0), (0, 2)), (2, (1, 1), (2, 1)), (2, (2, 1), (2, 1)),
    (2, (2, 1), (3, 1)), (2, (2, 1), (0, 2))] :
    Array (Fin 3 × (Fin 5 × ℕ) × (Fin 5 × ℕ)))[r.val]'r.isLt

/-- The constant class, the exceptional component, or the strict line. -/
def tailCurve (i : Fin 2) (r : Fin 68) : X.Curve :=
  ![0, X.exceptionalCurve i, BlowupTwoLineBP.line] (properProfile r).1

/-- The first relative marking at this proper-class key. -/
def tailFirst (i : Fin 2) (r : Fin 68) : SurfaceInsertion X :=
  ⟨label i (properProfile r).2.1.1, (properProfile r).2.1.2⟩

/-- The second relative marking at this proper-class key. -/
def tailSecond (i : Fin 2) (r : Fin 68) : SurfaceInsertion X :=
  ⟨label i (properProfile r).2.2.1, (properProfile r).2.2.2⟩

/-- Full marked ancestor key before evaluating its numerical coefficient. -/
def properKey (i : Fin 2) (r : Fin 68) : SurfaceAncestorKey X :=
  pairKey (tailCurve i r) (tailFirst i r) (tailSecond i r)

/-- Total cotangent degree at most one. -/
def lowIndex (k : Fin 26) : Fin 68 :=
  (#[0, 5, 6, 7, 8, 10, 11, 12, 13, 15, 16, 17, 18, 20, 25, 30, 35, 40, 41, 42, 43,
    54, 59, 60, 61, 62] : Array (Fin 68))[k.val]'k.isLt

/-- Both markings have precisely one cotangent power. -/
def productIndex (k : Fin 12) : Fin 68 :=
  (#[21, 22, 23, 45, 46, 47, 49, 50, 52, 64, 65, 66] : Array (Fin 68))[k.val]'k.isLt

/-- At least one marking carries two or more cotangent powers. -/
def squareIndex (k : Fin 30) : Fin 68 :=
  (#[1, 2, 3, 4, 9, 14, 19, 24, 26, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 44,
    48, 51, 53, 55, 56, 57, 58, 63, 67] : Array (Fin 68))[k.val]'k.isLt

/-- The three evaluation cases partition the entire proper frame. -/
theorem proper_partition (r : Fin 68) :
    (∃ k, lowIndex k = r) ∨ (∃ k, productIndex k = r) ∨ ∃ k, squareIndex k = r := by
  revert r
  decide +kernel

end AxiomaticGW.BlowupTwoRulingInterior
