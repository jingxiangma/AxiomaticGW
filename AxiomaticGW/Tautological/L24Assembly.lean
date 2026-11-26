/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Initial
public import AxiomaticGW.Tautological.L24Primitive
public import AxiomaticGW.Tautological.CotangentDimensionReplay

/-!
# Assembly of the checked L24 correction operations

The 71 corrections are actual decorated graph operations, and their complete
weighted sum is checked against the incoming 721-term candidate. The separate
`L24InitialClass` comparison handles component dimension zeros and cancelling
auxiliary columns at the level of realized classes. `L24Relation` composes
that comparison with the source geometry to prove validity of the full vector.
This file supplies the free-strata arithmetic and preservation of realized zero.
-/

@[expose] public section

namespace AxiomaticGW.L24Assembly
open RelationCertificate L24CorrectionsReplay

/-- Apply all 29 high-power, 37 rational-psi and five WDVV corrections. -/
noncomputable def assemble (q : StrataModule 2 (Fin 4)) : StrataModule 2 (Fin 4) :=
  L24Symmetry.average (q + (∑ i, highWeights i • L24HighPsi.corrections i) +
    ∑ i, rationalWeights i • L24RationalPsi.corrections i) +
      ∑ i, wdvvWeights i • L24WDVV.corrections i

/-- Exact free-strata assembly at the independently held initial coordinate vector. -/
theorem assemble_interpret :
    assemble (interpret L24Graphs.columns initialClaim) =
      interpret L24Graphs.columns fullClaim := by
  rw [← assembled_checked]
  simp only [assemble, assembled, L24HighPsi.corrections_eq_interpret,
    L24RationalPsi.corrections_eq_interpret, L24WDVV.corrections_eq_interpret,
    high_checked, rational_checked, wdvv_checked, ← L24Symmetry.average_interpret,
    map_add, map_sum, map_smul]

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R] {C : StableCurveCohomology R}
attribute [local instance] strataRealizationModule

/-- Assembly preserves a realized zero when its actual source operations realize to zero. -/
theorem assemble_vanishes (A : StrataRealization C 2 (Fin 4))
    (hl : ∀ p, A.RelabelCompatible A L24Symmetry.stableArity L24Symmetry.stableArity
      (L24Symmetry.labels p))
    (q : StrataModule 2 (Fin 4)) (hq : A.map q = 0)
    (hh : ∀ i, A.map (L24HighPsi.corrections i) = 0)
    (hr : ∀ i, A.map (L24RationalPsi.corrections i) = 0)
    (hw : ∀ i, A.map (L24WDVV.corrections i) = 0) : A.map (assemble q) = 0 := by
  have hbefore : A.map (q + (∑ i, highWeights i • L24HighPsi.corrections i) +
      ∑ i, rationalWeights i • L24RationalPsi.corrections i) = 0 := by
    simp only [map_add, map_sum, map_smul, hq, hh, hr, smul_zero,
      Finset.sum_const_zero, add_zero]
  rw [assemble, map_add, L24Symmetry.average_vanishes A hl _ hbefore]
  simp only [map_sum, map_smul, hw, smul_zero, Finset.sum_const_zero, add_zero]

end AxiomaticGW.L24Assembly
