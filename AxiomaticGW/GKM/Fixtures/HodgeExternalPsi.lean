/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeOneRealization
public import Mathlib.Tactic.Module

/-!
# The external-psi part of the actual degree-two Hodge candidate

Exactly positions 0, 1, 2, 9 and 15 of the original 28-column packet contain
external psi. They are the existing external psi operation applied to the
five original degree-one columns. The psi square occurs once; each of the
four mixed terms occurs twice. All original rational coefficients and both
ordered separating columns are retained.

This constructs and realizes that five-slot portion from the existing
external-psi law. The other 23 original occurrences remain an explicit
remainder. No identification with a Hodge square, boundary product, or
kappa product is an input or conclusion.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeExternalPsi

open AdmcyclesHodgeStrataCandidates
open scoped BigOperators

/-- One external cotangent factor at the unique original marking. -/
def externalPowers : Fin 1 → ℕ := fun _ ↦ 1

/-- The four original degree-one occurrences other than the external-psi term. -/
noncomputable def nonPsiSource : StrataModule 2 (Fin 1) :=
  raw_0_1_degree1Coordinates 1 • StrataModule.basis (raw_0_1_degree1Columns 1) +
    raw_0_1_degree1Coordinates 2 • StrataModule.basis (raw_0_1_degree1Columns 2) +
    raw_0_1_degree1Coordinates 3 • StrataModule.basis (raw_0_1_degree1Columns 3) +
    raw_0_1_degree1Coordinates 4 • StrataModule.basis (raw_0_1_degree1Columns 4)

/-- Retain the actual source coefficient and double only the mixed terms. -/
noncomputable def constructedPsiPart : StrataModule 2 (Fin 1) :=
  raw_0_1_degree1Coordinates 0 • StrataModule.mulLegPsi externalPowers
    (raw_0_1_degree1Coordinates 0 • StrataModule.basis (raw_0_1_degree1Columns 0) +
      (2 : ℚ) • nonPsiSource)

/-- The five actual target occurrences, in their original packet order. -/
noncomputable def packetPsiPart : StrataModule 2 (Fin 1) :=
  raw_1_1_degree2Coordinates 0 • StrataModule.basis (raw_1_1_degree2Columns 0) +
    raw_1_1_degree2Coordinates 1 • StrataModule.basis (raw_1_1_degree2Columns 1) +
    raw_1_1_degree2Coordinates 2 • StrataModule.basis (raw_1_1_degree2Columns 2) +
    raw_1_1_degree2Coordinates 9 • StrataModule.basis (raw_1_1_degree2Columns 9) +
    raw_1_1_degree2Coordinates 15 • StrataModule.basis (raw_1_1_degree2Columns 15)

/-- The original external psi column acquires its second, rather than a node, psi. -/
theorem rawGraph20_eq_psiSquare : rawGraph20 = rawGraph1.addLegPsi externalPowers := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- External psi multiplication retains the original positive kappa decoration. -/
theorem rawGraph7_eq_psiKappa : rawGraph7 = rawGraph2.addLegPsi externalPowers := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The new psi factor is at the old marking of the loop column. -/
theorem rawGraph8_eq_psiLoop : rawGraph8 = rawGraph3.addLegPsi externalPowers := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The first ordered separating occurrence retains its marked component. -/
theorem rawGraph6_eq_psiMarkedLeft : rawGraph6 = rawGraph4.addLegPsi externalPowers := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The second ordered separating occurrence is checked separately. -/
theorem rawGraph22_eq_psiMarkedRight : rawGraph22 = rawGraph5.addLegPsi externalPowers := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Bind the square coefficient once and each mixed coefficient with multiplicity two. -/
theorem actual_coefficients :
    raw_1_1_degree2Coordinates 15 = raw_0_1_degree1Coordinates 0 ^ 2 ∧
      raw_1_1_degree2Coordinates 9 =
        2 * raw_0_1_degree1Coordinates 0 * raw_0_1_degree1Coordinates 1 ∧
      raw_1_1_degree2Coordinates 0 =
        2 * raw_0_1_degree1Coordinates 0 * raw_0_1_degree1Coordinates 2 ∧
      raw_1_1_degree2Coordinates 1 =
        2 * raw_0_1_degree1Coordinates 0 * raw_0_1_degree1Coordinates 3 ∧
      raw_1_1_degree2Coordinates 2 =
        2 * raw_0_1_degree1Coordinates 0 * raw_0_1_degree1Coordinates 4 := by
  decide +kernel

/-- The graph operation constructs exactly the original five target occurrences. -/
theorem packetPsiPart_eq_constructed : packetPsiPart = constructedPsiPart := by
  change (-1 / 144 : ℚ) • StrataModule.basis rawGraph8 +
    (-1 / 144 : ℚ) • StrataModule.basis rawGraph6 +
    (-1 / 144 : ℚ) • StrataModule.basis rawGraph22 +
    (-1 / 72 : ℚ) • StrataModule.basis rawGraph7 +
    (1 / 144 : ℚ) • StrataModule.basis rawGraph20 =
    (-1 / 12 : ℚ) • StrataModule.mulLegPsi externalPowers
      ((-1 / 12 : ℚ) • StrataModule.basis rawGraph1 + (2 : ℚ) •
        ((1 / 12 : ℚ) • StrataModule.basis rawGraph2 +
          (1 / 24 : ℚ) • StrataModule.basis rawGraph3 +
          (1 / 24 : ℚ) • StrataModule.basis rawGraph4 +
          (1 / 24 : ℚ) • StrataModule.basis rawGraph5))
  simp only [map_add, map_smul, StrataModule.mulLegPsi_basis,
    ← rawGraph20_eq_psiSquare, ← rawGraph7_eq_psiKappa, ← rawGraph8_eq_psiLoop,
    ← rawGraph6_eq_psiMarkedLeft, ← rawGraph22_eq_psiMarkedRight]
  module

/-- Every original occurrence outside the five external-psi positions. -/
def remainderIndices : Fin 23 → Fin 28 :=
  ![3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The remainder retains its original columns and exact coefficients. -/
noncomputable def packetRemainder : StrataModule 2 (Fin 1) :=
  RelationCertificate.interpret (fun i ↦ raw_1_1_degree2Columns (remainderIndices i))
    (fun i ↦ raw_1_1_degree2Coordinates (remainderIndices i))

/-- All 28 occurrences are retained; this decomposition assumes no product validity. -/
theorem original_packet_decomposition :
    raw_1_1_degree2 = packetPsiPart + packetRemainder := by
  let f : Fin 28 → StrataModule 2 (Fin 1) := fun i ↦
    raw_1_1_degree2Coordinates i • StrataModule.basis (raw_1_1_degree2Columns i)
  have hrest :
      (∑ j ∈ ({0, 1, 2, 9, 15} : Finset (Fin 28))ᶜ, f j) =
        ∑ i : Fin 23, f (remainderIndices i) := by
    have hset : ({0, 1, 2, 9, 15} : Finset (Fin 28))ᶜ =
        Finset.univ.image remainderIndices := by decide +kernel
    have hinj : Function.Injective remainderIndices := by decide +kernel
    rw [hset]
    exact Finset.sum_image (fun _ _ _ _ he ↦ hinj he)
  have hpsi : (∑ j ∈ ({0, 1, 2, 9, 15} : Finset (Fin 28)), f j) =
      packetPsiPart := by
    rw [Finset.sum_insert (by decide : (0 : Fin 28) ∉ ({1, 2, 9, 15} : Finset (Fin 28))),
      Finset.sum_insert (by decide : (1 : Fin 28) ∉ ({2, 9, 15} : Finset (Fin 28))),
      Finset.sum_insert (by decide : (2 : Fin 28) ∉ ({9, 15} : Finset (Fin 28))),
      Finset.sum_insert (by decide : (9 : Fin 28) ∉ ({15} : Finset (Fin 28))), Finset.sum_singleton]
    change f 0 + (f 1 + (f 2 + (f 9 + f 15))) = (((f 0 + f 1) + f 2) + f 9) + f 15
    abel
  simp only [raw_1_1_degree2, packetRemainder, RelationCertificate.interpret_apply]
  change (∑ i, f i) = packetPsiPart + ∑ i : Fin 23, f (remainderIndices i)
  rw [← Finset.sum_add_sum_compl ({0, 1, 2, 9, 15} : Finset (Fin 28)) f, hpsi, hrest]

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R}

attribute [local instance] strataRealizationModule

/-- The constructed operation is actual multiplication by the external psi class. -/
theorem map_packetPsiPart (A : StrataRealization C 2 (Fin 1)) (P : PsiClasses C)
    (hpsi : A.LegPsiCompatible P HodgeDegreeOneRealization.stable) :
    A.map packetPsiPart = raw_0_1_degree1Coordinates 0 •
      ((raw_0_1_degree1Coordinates 0 •
          A.map (StrataModule.basis (raw_0_1_degree1Columns 0)) +
        (2 : ℚ) • A.map nonPsiSource) *
        P.psi 2 (Fin 1) HodgeDegreeOneRealization.stable 0) := by
  rw [packetPsiPart_eq_constructed, constructedPsiPart, map_smul,
    A.map_mulLegPsi P HodgeDegreeOneRealization.stable hpsi, map_add, map_smul, map_smul]
  simp only [PsiClasses.monomial, Fin.prod_univ_one, externalPowers, pow_one]

/-- Unit normalization identifies the square term; all four mixed source terms remain. -/
theorem map_packetPsiPart_normalized
    (A : StrataRealization C 2 (Fin 1)) (P : PsiClasses C)
    (hpsi : A.LegPsiCompatible P HodgeDegreeOneRealization.stable)
    (hfund : A.map (StrataModule.basis (TautologicalStratum.fundamental 2 (Fin 1)
      HodgeDegreeOneRealization.stable)) = 1) :
    A.map packetPsiPart =
      (1 / 144 : ℚ) • (P.psi 2 (Fin 1) HodgeDegreeOneRealization.stable 0) ^ 2 +
      (-1 / 6 : ℚ) • (A.map nonPsiSource *
        P.psi 2 (Fin 1) HodgeDegreeOneRealization.stable 0) := by
  have hbase : A.map (StrataModule.basis rawGraph1) =
      P.psi 2 (Fin 1) HodgeDegreeOneRealization.stable 0 := by
    rw [HodgeDegreeOneRealization.rawGraph1_eq_psi,
      A.map_addLegPsi P HodgeDegreeOneRealization.stable hpsi, hfund, one_mul]
    simp only [PsiClasses.monomial, Fin.prod_univ_one, pow_one]
  rw [map_packetPsiPart A P hpsi]
  change (-1 / 12 : ℚ) • (((-1 / 12 : ℚ) • A.map (StrataModule.basis rawGraph1) +
    (2 : ℚ) • A.map nonPsiSource) * _) = _
  rw [hbase]
  simp only [add_mul, smul_add, smul_mul_assoc, smul_smul]
  norm_num [pow_two]

end AxiomaticGW.GKM.HodgeExternalPsi
