/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedGluing
public import AxiomaticGW.Tautological.RationalTail

/-!
# Finite signed pullbacks of cotangent-decorated gluing expressions

The existing expression and its component powers are retained. Equality
decisions on original component labels are supplied as computational data;
this avoids classical choices when constructing explicit correction graphs.
Multisets keep every repeated placement with its integer coefficient.

At each component there is one positive placement, and one negative rational
tail for each positive power. The tail retains the old and new labels; the
old power, decreased by one, stays at the main attaching flag. Subsequent
raw gluings keep their original node flags through the existing bijections.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

/-- Equality decisions needed to construct a tail at an original component label. -/
@[reducible] def DecidableLabels {g : ℕ} {S : Type} [Fintype S] :
    GluingExpression g S → Type
  | @fundamental _ S _ _ => DecidableEq S
  | @relabel _ _ _ _ _ _ x => x.DecidableLabels
  | @separating _ _ _ _ _ _ x y => x.DecidableLabels × y.DecidableLabels
  | @nonseparating _ _ _ x => x.DecidableLabels

/-- An existing decorated expression together with decisions for executable pullback. -/
structure CotangentTerm (g : ℕ) (S : Type) [Fintype S] where
  /-- Original raw gluing construction. -/
  expression : GluingExpression g S
  /-- Powers at all component labels, including future node branches. -/
  decoration : expression.CotangentDecoration
  /-- Computational label decisions, with no geometric assumptions. -/
  labels : expression.DecidableLabels

namespace CotangentTerm

/-- A component monomial with its given finite label decisions. -/
def fundamental (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity g S) (d : S → ℕ) : CotangentTerm g S :=
  ⟨.fundamental g S h, d, inferInstance⟩

/-- Transport external labels, retaining the original component data. -/
def relabel {g : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (e : S ≃ T) (z : CotangentTerm g S) : CotangentTerm g T :=
  ⟨z.expression.relabel e, z.decoration, z.labels⟩

/-- The same raw separating operation, with both branch decorations. -/
def separating {g₁ g₂ : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (x : CotangentTerm g₁ (Option S)) (y : CotangentTerm g₂ (Option T)) :
    CotangentTerm (g₁ + g₂) (S ⊕ T) :=
  ⟨x.expression.separating y.expression, (x.decoration, y.decoration), (x.labels, y.labels)⟩

/-- The same raw nonseparating operation, keeping both original node flags. -/
def nonseparating {g : ℕ} {S : Type} [Fintype S]
    (x : CotangentTerm g (Option (Option S))) : CotangentTerm (g + 1) S :=
  ⟨x.expression.nonseparating, x.decoration, x.labels⟩

/-- One new rational tail, with the reduced old power at its main attaching flag. -/
def tail {g : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity g S) (d : S → ℕ) (s : S) : CotangentTerm g (Option S) :=
  (((fundamental g S h (Function.update d s (d s - 1))).relabel
    (Equiv.optionSubtypeNe s).symm).separating
      (fundamental 0 (Option Bool) PsiBoundaryExpansion.tailStable (fun _ ↦ 0))).relabel
        (PsiBoundaryExpansion.tailLabels s)

end CotangentTerm

/-- One universal-curve pullback, as explicit signed decorated expressions. -/
def addCotangentMarking {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → x.DecidableLabels →
      Multiset (ℤ × CotangentTerm g (Option S))
  | @fundamental g S _ h, d, l =>
      letI := l
      {(1, CotangentTerm.fundamental g (Option S) h.option (fun s ↦ s.elim 0 d))} +
        (Finset.univ.filter (fun s ↦ d s ≠ 0)).val.map
          (fun s ↦ (-1, CotangentTerm.tail h d s))
  | @relabel _ _ _ _ _ e x, d, l =>
      (x.addCotangentMarking d l).map fun z ↦ (z.1, z.2.relabel e.optionCongr)
  | @separating _ _ S T _ _ x y, d, l =>
      ((x.addCotangentMarking d.1 l.1).map fun z ↦ (z.1,
        ((z.2.relabel (swapDoubleOption S)).separating ⟨y, d.2, l.2⟩).relabel
          (optionSumEquivLeft S T).symm)) +
      ((y.addCotangentMarking d.2 l.2).map fun z ↦ (z.1,
        ((CotangentTerm.mk x d.1 l.1).separating (z.2.relabel (swapDoubleOption T))).relabel
          (optionSumEquivRight S T).symm))
  | @nonseparating _ S _ x, d, l =>
      (x.addCotangentMarking d l).map fun z ↦
        (z.1, (z.2.relabel (forgetNonseparatingEquiv S).symm).nonseparating)

namespace CotangentTerm

/-- Executable one-marking expansion of the bundled existing term. -/
def addMarking {g : ℕ} {S : Type} [Fintype S] (z : CotangentTerm g S) :
    Multiset (ℤ × CotangentTerm g (Option S)) :=
  z.expression.addCotangentMarking z.decoration z.labels

/-- Iterate the signed expansion, multiplying coefficients and preserving multiplicities. -/
def addMarkings {g : ℕ} {S : Type} [Fintype S] (z : CotangentTerm g S) :
    (n : ℕ) → Multiset (ℤ × CotangentTerm g (ExtraMarkings n S))
  | 0 => {(1, z)}
  | n + 1 => (z.addMarkings n).bind fun t ↦
      t.2.addMarking.map fun w ↦ (t.1 * w.1, w.2)

end CotangentTerm

end AxiomaticGW.GluingExpression
