/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCoefficients
public import AxiomaticGW.Surfaces.GenusTwoLeadingTerms

/-!
# Executable coefficients of the complete BP and L24 families

The requested variable may have a smaller full curve class than the equation.
`GenusTwoCoefficientRelations` proves equality with the existing normalized
equations without imposing the initialization cost of their source proofs.
-/

@[expose] public section

namespace AxiomaticGW
open RelationCertificate PsiBoundaryExpansion SurfacePolynomialReduction

namespace BelorousskiPandharipande

/-- Extract a coefficient, including positive-class complements and calibration tails.
The other sixteen diagrams have no genus-two component; their coefficients vanish. -/
def normalizedCoefficient (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    (v : Variable X) : ℚ :=
  ∑ i : Fin 4, rawPaperCoefficient (Fin.castAdd 16 i) * ∑ e,
    (((orbitCotangentTerm (Fin.castAdd 16 i) e).addMarkings n).map fun t ↦ (t.1 : ℚ) *
      SurfaceGenusTwo.coefficientEval X v t.2.expression (by omega)
        t.2.decoration beta k a).sum

end BelorousskiPandharipande

namespace L24Relation

set_option maxRecDepth 20000

/-- Extract a coefficient from all source terms and signed marking pullbacks. -/
def normalizedCoefficient (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (v : Variable X) : ℚ :=
  ((cotangentRelation.pullback n).map fun t ↦ t.1 *
    SurfaceGenusTwo.coefficientEval X v t.2.expression (by omega)
      t.2.decoration beta k a).sum

end L24Relation
end AxiomaticGW
