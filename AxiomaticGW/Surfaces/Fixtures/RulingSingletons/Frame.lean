/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleLineSingletons.Third
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.Fourth

/-! # Lower-genus vertex keys in the two ruling classes of the two-point blowup

The ruling `Eᵢ + L` has two distinct positive primitive summands. Its one-marking
squares use the same marked profiles as the double strict line. Here we reuse
only those marked profiles, preserving the full curve on every subsequent lookup.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling
open SurfaceGenusTwoPositiveSquare

/-- The projective plane blown up at the two fixed points. -/
abbrev X := SurfaceTarget.blowupTwo

/-- The pencil of lines through the other blown-up point, in effective coordinates. -/
def curve (i : Fin 2) : X.Curve := X.exceptionalCurve i + BlowupTwoLineBP.line

/-- Basis labels ordered by unit, hyperplane, the indicated exceptional divisor, its
opposite exceptional divisor, and point. -/
def label (i : Fin 2) (j : Fin 5) : SurfaceBasisLabel X :=
  ![.unit, .hyperplane, .exceptional i, .exceptional i.rev, .point] j

/-- Carry a marked profile to this ruling, exchanging exceptional labels on the second axis. -/
def rulingKey (i : Fin 2) (q : SurfaceAncestorKey X) : SurfaceAncestorKey X where
  genus := q.genus
  beta := curve i
  insertions := q.insertions.map fun a ↦
    { a with label := match a.label with
      | .exceptional j => .exceptional (if i = 0 then j else j.rev)
      | b => b }
  stable := by simpa only [Multiset.card_map] using q.stable

/-- Use the original exceptional backend on the exceptional summand, and the checked
strict-line backend on the other proper classes. Both agree on every input with the
same global low-genus recursion. -/
def initial (i : Fin 2) : CertifiedComponents X where
  value q := if q.beta = X.exceptionalCurve i then
    (BlowupTwoDoubleExceptionalInteriorPairs.Fourth.backend i).value q
    else BlowupTwoDoubleLineComponents.Third.backend.value q
  sound q := by
    split
    · exact (BlowupTwoDoubleExceptionalInteriorPairs.Fourth.backend i).sound q
    · exact BlowupTwoDoubleLineComponents.Third.backend.sound q

/-- Cache only full ruling vertices at one cotangent degree. Primitive and constant
vertices continue to use the backend already verified for those classes. -/
def fullLayer (i : Fin 2) (c : CertifiedComponents X) (power : ℕ)
    (pool : ℕ → List (Entry X)) : CertifiedComponents X where
  value q := if q.totalPsi = power ∧ q.beta = curve i then
    stageLookup (SurfaceLowGenusPointCache.stagedValue c.value) q (pool (slot q))
    else c.value q
  sound q := by
    split
    · exact stageLookup_eq _ (SurfaceLowGenusPointCache.stagedValue_eq c.sound) q _
    · exact c.sound q

end AxiomaticGW.BlowupTwoRuling
