/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeLoopSeparatingProduct

/-!
# The genus-two Picard relation on the one-marked Hodge packet

In the full stable genus-two, one-marked, codimension-one 3-spin frame, the
original generator has coefficients `[-30, 30, 42, 3]` on kappa, marked psi,
separating and loop raw pushforwards. The marked separating graph has one
presentation up to isomorphism. The loop pushforward counts both node branches.

The equality of free strata below retains the original row as its residual.
Its geometric use requires a realization killing that row. The source theorem
is Pandharipande, Pixton and Zvonkine, [Relations on the moduli space of stable
curves via 3-spin structures](https://arxiv.org/abs/1303.1043). In the pinned
Sage environment, `python -B scripts/check_admcycles_hodge_picard.py` verifies
the original row directly from its generator parameter and matches the five
source graph terms to the saved packet.
-/

@[expose] public section
namespace AxiomaticGW.GKM.HodgeGenusTwoPicard
open AdmcyclesHodgeStrataCandidates RelationCertificate

/-- Ordered columns in the original `admcycles` monomial frame. -/
def columns : Fin 4 → TautologicalStratum 2 (Fin 1) :=
  ![rawGraph2, rawGraph1, rawGraph4, rawGraph3]

/-- The unique original full-stable PPZ row, with empty partition and marking weight zero. -/
def row : Coordinates 4 := ![-30, 30, 42, 3]

/-- The pullback of the discriminant's boundary expression
`δ_irr + 2 δ_1` in the raw gluing convention. -/
noncomputable def boundary : StrataModule 2 (Fin 1) :=
  (1 / 2 : ℚ) • StrataModule.basis rawGraph3 + (2 : ℚ) • StrataModule.basis rawGraph4

/-- The difference between ten copies of the actual degree-one packet and the two
boundary terms is exactly minus one thirty-sixth of the original generator. -/
theorem raw_residual :
    (10 : ℚ) • raw01Degree1 - boundary = (-1 / 36 : ℚ) • interpret columns row := by
  simp only [raw01Degree1, interpret_apply, boundary, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.isValue, raw01Degree1Columns, raw01Degree1Coordinates,
    columns, row, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    HodgeLoopSeparatingProduct.rawGraph5_eq_rawGraph4, smul_add, smul_smul, add_zero]
  module

/-- Every linear interpretation killing the original 3-spin row reads the held
degree-one packet as one tenth of the discriminant boundary. -/
theorem map_degree_one {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ev : StrataModule 2 (Fin 1) →ₗ[ℚ] V) (hrow : ev (interpret columns row) = 0) :
    ev raw01Degree1 = (1 / 10 : ℚ) • ev boundary := by
  have he := congrArg ev raw_residual
  rw [map_sub, map_smul, map_smul, hrow, smul_zero, sub_eq_zero] at he
  rw [← he, smul_smul]
  norm_num

/-- In particular the identity holds in the free strata quotient by the single original row. -/
theorem quotient_degree_one :
    let rels := Submodule.span ℚ ({interpret columns row} : Set (StrataModule 2 (Fin 1)))
    StrataModule.quotientMk rels raw01Degree1 =
      (1 / 10 : ℚ) • StrataModule.quotientMk rels boundary := by
  apply map_degree_one
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.subset_span (Set.mem_singleton _)

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- The boundary is the half-loop and twice the marked separating Gysin classes. -/
theorem map_boundary (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (hloop : HodgeDegreeOneRealization.loop.Compatible A F N)
    (hsep : HodgeDegreeOneRealization.separatingMarkedLeft.Compatible A F N) :
    (A 2 (Fin 1)).map boundary =
      (1 / 2 : ℚ) • HodgeDegreeOneRealization.loop.classValue F N +
      (2 : ℚ) • HodgeDegreeOneRealization.separatingMarkedLeft.classValue F N := by
  rw [boundary, map_add, map_smul, map_smul, HodgeDegreeOneRealization.rawGraph3_eq_loop,
    HodgeDegreeOneRealization.rawGraph4_eq_left,
    HodgeDegreeOneRealization.loop.map_stratum_eq_classValue A F N hloop,
    HodgeDegreeOneRealization.separatingMarkedLeft.map_stratum_eq_classValue A F N hsep]

end AxiomaticGW.GKM.HodgeGenusTwoPicard
