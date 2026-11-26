/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPointCoefficients

/-!
# Equal external labels in the compressed genus-two BP coefficients

All six original relabellings contribute the same scalar when the three
external basis classes coincide. The point pullbacks and the requested
singleton variable remain unchanged.
-/

@[expose] public section
namespace AxiomaticGW.BelorousskiPandharipande

/-- Compute one representative with multiplicity six for each genus-two BP diagram. -/
theorem pointCoefficient_eq_six_paperSum (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : SurfaceBasisLabel X) (v : SurfacePolynomialReduction.Variable X) :
    pointCoefficient X n beta (fun _ ↦ a) v =
      ∑ i : Fin 4, rawPaperCoefficient (Fin.castAdd 16 i) *
        (6 * SurfaceGenusTwo.pointCoefficient X v (paperCotangentTerm (Fin.castAdd 16 i))
          beta n (fun _ ↦ a)) := by
  have h (i : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (orbitCotangentTerm i e) beta n (fun _ ↦ a) =
        SurfaceGenusTwo.pointCoefficient X v (paperCotangentTerm i) beta n (fun _ ↦ a) := by
    simp only [orbitCotangentTerm, GluingExpression.CotangentTerm.relabel,
      SurfaceGenusTwo.pointCoefficient, GluingExpression.maxComponentGenus,
      GluingExpression.pointContraction]
    rfl
  simp only [pointCoefficient, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat]

end AxiomaticGW.BelorousskiPandharipande
