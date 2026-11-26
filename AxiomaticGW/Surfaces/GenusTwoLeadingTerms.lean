/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoLeading
public import AxiomaticGW.Surfaces.BelorousskiPandharipande
public import AxiomaticGW.Surfaces.L24Terms

/-!
# Executable leading entries for BP and L24

The runtime depends on the complete relation terms and gluing evaluator.
`GenusTwoLeadingRelations` proves equality to the fully normalized equations
without making native execution initialize the original source-proof assembly.
-/

@[expose] public section

namespace AxiomaticGW
open RelationCertificate PsiBoundaryExpansion SurfacePolynomialReduction

namespace BelorousskiPandharipande

/-- A BP matrix entry computed directly from decorated gluing. -/
def leadingCoefficient (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    (v : Variable X) : ℚ :=
  ∑ i, rawPaperCoefficient i * ∑ e,
    (((orbitCotangentTerm i e).addMarkings n).map fun t ↦ (t.1 : ℚ) *
      SurfaceGenusTwo.leadingCoefficientEval X beta v t.2.expression (by omega)
        t.2.decoration k a).sum

end BelorousskiPandharipande

namespace L24Relation

set_option maxRecDepth 20000

/-- A complete L24 matrix entry, with all 721 nonzero source terms retained. -/
def leadingCoefficient (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (v : Variable X) : ℚ :=
  ((cotangentRelation.pullback n).map fun t ↦ t.1 *
    SurfaceGenusTwo.leadingCoefficientEval X beta v t.2.expression (by omega)
      t.2.decoration k a).sum

end L24Relation
end AxiomaticGW
