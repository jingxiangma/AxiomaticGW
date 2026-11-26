/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeOneRealization
public import AxiomaticGW.Tautological.NonseparatingNodeNormal

/-!
# Two actual degree-two Hodge packet occurrences at a loop node

Positions 3 and 4 of the original 28-column degree-two expression are the two
ordered loop-branch psi decorations. Each retains its coefficient `-1/288`.
They are constructed from the genus-one corolla by the existing psi operation
and raw nonseparating gluing, then identified with the signed node expression.

This accepts neither a boundary self-intersection identity nor the entire
product represented by the packet. Other common-refinement terms and their
multiplicities remain separate obligations. No geometric Hodge class is named.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeNodeNormal

open AdmcyclesHodgeStrataCandidates

/-- Source of the actual genus-two nonseparating column; node markings are ordered. -/
noncomputable def source : TautologicalStratum 1 (Option (Option (Fin 1))) :=
  TautologicalStratum.fundamental 1 (Option (Option (Fin 1)))
    (StableArity.double_option_iff.mpr HodgeDegreeOneRealization.stable)

/-- Bind branch zero to its actual packet graph. -/
theorem rawGraph9_eq_first :
    rawGraph9 = (source.addLegPsi NonseparatingNode.firstPowers).nonseparating := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Bind branch one independently, retaining the packet's ordered occurrence. -/
theorem rawGraph23_eq_second :
    rawGraph23 = (source.addLegPsi NonseparatingNode.secondPowers).nonseparating := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The original two slots and coefficients, without merging their occurrences. -/
noncomputable def packetNodePair : StrataModule 2 (Fin 1) :=
  raw11Degree2Coordinates 3 • StrataModule.basis (raw11Degree2Columns 3) +
    raw11Degree2Coordinates 4 • StrataModule.basis (raw11Degree2Columns 4)

/-- The exact packet occurrences are a fixed rational multiple of the constructed
normal expression. No assumption about multiplication of raw classes is used. -/
theorem packetNodePair_eq :
    packetNodePair = (1 / 288 : ℚ) •
      StrataModule.nonseparatingNodeNormal (StrataModule.basis source) := by
  change (-1 / 288 : ℚ) • StrataModule.basis rawGraph23 +
    (-1 / 288 : ℚ) • StrataModule.basis rawGraph9 = _
  rw [StrataModule.nonseparatingNodeNormal_basis,
    ← rawGraph9_eq_first, ← rawGraph23_eq_second, smul_neg, smul_add]
  have hq : (-1 / 288 : ℚ) = -(1 / 288 : ℚ) := by norm_num
  simp only [hq, neg_smul]
  abel

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- Under existing primitive laws, the actual two coefficients multiply the raw
pushforward of the negative sum of the two source cotangent classes. -/
theorem map_packetNodePair
    (A : StrataRealization C 1 (Option (Option (Fin 1))))
    (B : StrataRealization C 2 (Fin 1))
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (hglue : A.NonseparatingCompatible B N HodgeDegreeOneRealization.stable)
    (hpsi : A.LegPsiCompatible P
      (StableArity.double_option_iff.mpr HodgeDegreeOneRealization.stable))
    (hfund : A.map (StrataModule.basis source) = 1) :
    B.map packetNodePair = (1 / 288 : ℚ) •
      N.push 1 (Fin 1) HodgeDegreeOneRealization.stable
        (-(P.psi 1 (Option (Option (Fin 1)))
            (StableArity.double_option_iff.mpr HodgeDegreeOneRealization.stable) none +
          P.psi 1 (Option (Option (Fin 1)))
            (StableArity.double_option_iff.mpr HodgeDegreeOneRealization.stable)
            (some none))) := by
  rw [packetNodePair_eq, map_smul,
    A.map_nonseparatingNodeNormal B N P HodgeDegreeOneRealization.stable hglue hpsi,
    hfund, one_mul]

end AxiomaticGW.GKM.HodgeNodeNormal
