/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataCandidates
public import AxiomaticGW.GKM.FixedPointTFT
public import AxiomaticGW.Tautological.StrataRealizationDegree
public import AxiomaticGW.Tautological.GraphIsomorphisms
public import AxiomaticGW.Tautological.BasicStrata
public import Mathlib.Tactic.NormNum

/-!
# Connected degree-zero normalization of the complete raw Hodge-packet assembly

All nine ordered pairs and all five recorded codimension components occur in
the assembled class. Coefficients remain supplied exact field elements. The
only normalization input on the realization is that the fundamental class
maps to one. The degree-zero coefficient at each fixed point is explicitly
bound to its Euler factor; positive-degree coefficients are retained.

This is a normalization theorem for the actual formal candidate expressions.
It does not identify them with Hodge classes or GW classes, construct their
geometric product, or prove CohFT gluing. Codimension here is the stable-curve
grading over the coefficient field, not a total equivariant grading or an
ordinary specialization of that field.
-/

@[expose] public section

namespace AxiomaticGW.AdmcyclesHodgeStrataNormalization

open scoped BigOperators
open AdmcyclesHodgeStrataCandidates

universe u

/-- Stable genus two with the one external label retained by the packet. -/
theorem stable : StableArity 2 (Fin 1) := by
  norm_num only [StableArity, Fintype.card_fin]

/-- Exactly the 45 existing decoded source expressions, including every empty component. -/
noncomputable def rawComponent : Fin 3 → Fin 3 → Fin 5 → StrataModule 2 (Fin 1) :=
  ![
    ![
      ![raw_0_0_degree0, raw_0_0_degree1, raw_0_0_degree2, raw_0_0_degree3, raw_0_0_degree4],
      ![raw_0_1_degree0, raw_0_1_degree1, raw_0_1_degree2, raw_0_1_degree3, raw_0_1_degree4],
      ![raw_0_2_degree0, raw_0_2_degree1, raw_0_2_degree2, raw_0_2_degree3, raw_0_2_degree4]
    ],
    ![
      ![raw_1_0_degree0, raw_1_0_degree1, raw_1_0_degree2, raw_1_0_degree3, raw_1_0_degree4],
      ![raw_1_1_degree0, raw_1_1_degree1, raw_1_1_degree2, raw_1_1_degree3, raw_1_1_degree4],
      ![raw_1_2_degree0, raw_1_2_degree1, raw_1_2_degree2, raw_1_2_degree3, raw_1_2_degree4]
    ],
    ![
      ![raw_2_0_degree0, raw_2_0_degree1, raw_2_0_degree2, raw_2_0_degree3, raw_2_0_degree4],
      ![raw_2_1_degree0, raw_2_1_degree1, raw_2_1_degree2, raw_2_1_degree3, raw_2_1_degree4],
      ![raw_2_2_degree0, raw_2_2_degree1, raw_2_2_degree2, raw_2_2_degree3, raw_2_2_degree4]
    ]
  ]

/-- The degree assertion is proved for each actual source component, not supplied by a packet. -/
theorem rawComponent_mem_degree (a b : Fin 3) (d : Fin 5) :
    rawComponent a b d ∈ StrataModule.degree d.val := by
  fin_cases a <;> fin_cases b <;> fin_cases d
  · exact raw_0_0_degree0_mem_degree
  · exact raw_0_0_degree1_mem_degree
  · exact raw_0_0_degree2_mem_degree
  · exact raw_0_0_degree3_mem_degree
  · exact raw_0_0_degree4_mem_degree
  · exact raw_0_1_degree0_mem_degree
  · exact raw_0_1_degree1_mem_degree
  · exact raw_0_1_degree2_mem_degree
  · exact raw_0_1_degree3_mem_degree
  · exact raw_0_1_degree4_mem_degree
  · exact raw_0_2_degree0_mem_degree
  · exact raw_0_2_degree1_mem_degree
  · exact raw_0_2_degree2_mem_degree
  · exact raw_0_2_degree3_mem_degree
  · exact raw_0_2_degree4_mem_degree
  · exact raw_1_0_degree0_mem_degree
  · exact raw_1_0_degree1_mem_degree
  · exact raw_1_0_degree2_mem_degree
  · exact raw_1_0_degree3_mem_degree
  · exact raw_1_0_degree4_mem_degree
  · exact raw_1_1_degree0_mem_degree
  · exact raw_1_1_degree1_mem_degree
  · exact raw_1_1_degree2_mem_degree
  · exact raw_1_1_degree3_mem_degree
  · exact raw_1_1_degree4_mem_degree
  · exact raw_1_2_degree0_mem_degree
  · exact raw_1_2_degree1_mem_degree
  · exact raw_1_2_degree2_mem_degree
  · exact raw_1_2_degree3_mem_degree
  · exact raw_1_2_degree4_mem_degree
  · exact raw_2_0_degree0_mem_degree
  · exact raw_2_0_degree1_mem_degree
  · exact raw_2_0_degree2_mem_degree
  · exact raw_2_0_degree3_mem_degree
  · exact raw_2_0_degree4_mem_degree
  · exact raw_2_1_degree0_mem_degree
  · exact raw_2_1_degree1_mem_degree
  · exact raw_2_1_degree2_mem_degree
  · exact raw_2_1_degree3_mem_degree
  · exact raw_2_1_degree4_mem_degree
  · exact raw_2_2_degree0_mem_degree
  · exact raw_2_2_degree1_mem_degree
  · exact raw_2_2_degree2_mem_degree
  · exact raw_2_2_degree3_mem_degree
  · exact raw_2_2_degree4_mem_degree

/-- The actual raw zero graph is the existing fundamental stratum. -/
theorem rawGraph0_eq_fundamental :
    rawGraph0 = TautologicalStratum.fundamental 2 (Fin 1) stable :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      rawIncidence0Candidate rawIncidence0Valid rawGraph0Exponents)
    (DecoratedStableGraph.oneVertex_totalGenus 2 (Fin 1) stable 0 (fun _ ↦ 0))
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- The complete raw (0,0), degree-zero expression is one fundamental basis vector. -/
theorem raw_0_0_degree0_eq_fundamental :
    raw_0_0_degree0 =
      StrataModule.basis (TautologicalStratum.fundamental 2 (Fin 1) stable) := by
  rw [raw_0_0_degree0, RelationCertificate.interpret_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1 : ℚ) • StrataModule.basis rawGraph0 + 0 = _
  rw [one_smul, add_zero, rawGraph0_eq_fundamental]

/-- All eight other actual degree-zero source components are explicitly empty. -/
theorem rawComponent_degree_zero (a b : Fin 3) :
    rawComponent a b 0 = if a = 0 ∧ b = 0 then
      StrataModule.basis (TautologicalStratum.fundamental 2 (Fin 1) stable) else 0 := by
  fin_cases a <;> fin_cases b
  · exact raw_0_0_degree0_eq_fundamental
  · change raw_0_1_degree0 = 0
    rw [raw_0_1_degree0, RelationCertificate.interpret_apply]
    exact Fin.sum_univ_zero _
  · change raw_0_2_degree0 = 0
    rw [raw_0_2_degree0, RelationCertificate.interpret_apply]
    exact Fin.sum_univ_zero _
  · change raw_1_0_degree0 = 0
    rw [raw_1_0_degree0, RelationCertificate.interpret_apply]
    exact Fin.sum_univ_zero _
  · change raw_1_1_degree0 = 0
    rw [raw_1_1_degree0, RelationCertificate.interpret_apply]
    exact Fin.sum_univ_zero _
  · change raw_1_2_degree0 = 0
    rw [raw_1_2_degree0, RelationCertificate.interpret_apply]
    exact Fin.sum_univ_zero _
  · change raw_2_0_degree0 = 0
    rw [raw_2_0_degree0, RelationCertificate.interpret_apply]
    exact Fin.sum_univ_zero _
  · change raw_2_1_degree0 = 0
    rw [raw_2_1_degree0, RelationCertificate.interpret_apply]
    exact Fin.sum_univ_zero _
  · change raw_2_2_degree0 = 0
    rw [raw_2_2_degree0, RelationCertificate.interpret_apply]
    exact Fin.sum_univ_zero _

variable {K : Type u} [Field K] [Algebra ℚ K]
  {C : StableCurveCohomology K}

attribute [local instance] strataRealizationModule

/-- Projection of all actual components uses only homogeneous realization and unit normalization. -/
theorem scalar_rawComponent (D : ConnectedDegreeZero C)
    (A : StrataRealization C 2 (Fin 1))
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1)
    (a b : Fin 3) (d : Fin 5) :
    D.scalar 2 (Fin 1) stable (A.map (rawComponent a b d)) =
      if d = 0 then (if a = 0 ∧ b = 0 then 1 else 0) else 0 := by
  by_cases hd : d = 0
  · subst d
    rw [if_pos rfl, rawComponent_degree_zero]
    by_cases hab : a = 0 ∧ b = 0
    · rw [if_pos hab, hfund, map_one, if_pos hab]
    · rw [if_neg hab, map_zero, map_zero, if_neg hab]
  · rw [if_neg hd]
    have hv : d.val ≠ 0 := by
      intro hz
      exact hd (Fin.ext hz)
    exact D.scalar_map_eq_zero_of_mem_degree A stable hv (rawComponent_mem_degree a b d)

variable {ι : Type*} [Fintype ι]

/-- Every fixed locus, ordered pair and recorded degree component occurs in the sum. -/
noncomputable def assembly (A : StrataRealization C 2 (Fin 1))
    (coeff : ι → Fin 3 → Fin 3 → K) : C.H 2 (Fin 1) :=
  ∑ p, ∑ a, ∑ b, ∑ d : Fin 5, coeff p a b • A.map (rawComponent a b d)

/-- The complete assembly projects to its actual (0,0), degree-zero coefficients. -/
theorem scalar_assembly (D : ConnectedDegreeZero C)
    (A : StrataRealization C 2 (Fin 1))
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1)
    (coeff : ι → Fin 3 → Fin 3 → K) :
    D.scalar 2 (Fin 1) stable (assembly A coeff) = ∑ p, coeff p 0 0 := by
  simp only [assembly, map_sum, map_smul, scalar_rawComponent D A hfund,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue, Fin.succ_ne_zero,
    add_zero, and_true, and_false, ite_true, ite_false, mul_one, mul_zero]

/-- Matching the held Euler coefficients gives the existing canonical genus-two TFT value. -/
theorem scalar_assembly_eq_tft [DecidableEq ι] (D : ConnectedDegreeZero C)
    (A : StrataRealization C 2 (Fin 1))
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1)
    (coeff : ι → Fin 3 → Fin 3 → K) (euler : ι → Kˣ)
    (h00 : ∀ p, coeff p 0 0 = (euler p : K)) :
    D.scalar 2 (Fin 1) stable (assembly A coeff) =
      (GKM.FixedPointAlgebra.algebra euler).correlator 2 (Fin 1) (fun _ ↦ 1) := by
  rw [scalar_assembly D A hfund, GKM.FixedPointTFT.correlator_two_unit]
  exact Finset.sum_congr rfl (fun p _ ↦ h00 p)

end AxiomaticGW.AdmcyclesHodgeStrataNormalization
