module

public import AxiomaticGW.GKM.AdmcyclesHodgeStrataNormalization

/-! The actual full component frame is retained before connected degree-zero projection. -/

@[expose] public section

namespace AxiomaticGWTest.GKM.AdmcyclesHodgeStrataNormalization

open AxiomaticGW AdmcyclesHodgeStrataNormalization AdmcyclesHodgeStrataCandidates
open scoped BigOperators

universe u

/-- The frame includes the complete top-degree expression before scalar projection. -/
theorem top_component_retained : rawComponent 2 2 4 = raw_2_2_degree4 := rfl

/-- Both complete ordered mixed expressions remain separate source entries. -/
theorem ordered_components_retained :
    rawComponent 1 2 3 = raw_1_2_degree3 ∧ rawComponent 2 1 3 = raw_2_1_degree3 :=
  ⟨rfl, rfl⟩

/-- All 45 source expressions carry their checked stable-curve codimension. -/
theorem full_component_degree (a b : Fin 3) (d : Fin 5) :
    rawComponent a b d ∈ StrataModule.degree d.val := rawComponent_mem_degree a b d

variable {K : Type u} [Field K] [Algebra ℚ K] {C : StableCurveCohomology K}

attribute [local instance] strataRealizationModule

/-- The nontrivial 122-term raw expression has zero scalar projection by its degree alone. -/
theorem mixed_positive_scalar_zero (D : ConnectedDegreeZero C)
    (A : StrataRealization C 2 (Fin 1)) :
    D.scalar 2 (Fin 1) stable (A.map raw_1_2_degree3) = 0 :=
  D.scalar_map_eq_zero_of_mem_degree A stable (by decide) raw_1_2_degree3_mem_degree

/-- Rational linear combinations, not only individual basis graphs, realize in the same degree. -/
theorem linear_combination_degree (A : StrataRealization C 2 (Fin 1))
    (q : ℚ) {d : ℕ} {x y : StrataModule 2 (Fin 1)}
    (hx : x ∈ StrataModule.degree d) (hy : y ∈ StrataModule.degree d) :
    A.map (q • x + y) ∈ (C.H 2 (Fin 1)).degree d :=
  A.map_mem_degree ((StrataModule.degree d).add_mem
    ((StrataModule.degree d).smul_mem q hx) hy)

/-- Empty fixed-point index type gives an empty complete assembly. -/
theorem empty_loci (A : StrataRealization C 2 (Fin 1))
    (coeff : Empty → Fin 3 → Fin 3 → K) : assembly A coeff = 0 := by
  simp only [assembly, Fintype.sum_empty]

/-- Changed positive-degree coefficients preserve this projection; no class equality is asserted. -/
theorem same_zero_coordinates_same_projection {ι : Type*} [Fintype ι]
    (D : ConnectedDegreeZero C) (A : StrataRealization C 2 (Fin 1))
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1)
    (c c' : ι → Fin 3 → Fin 3 → K) (h00 : ∀ p, c p 0 0 = c' p 0 0) :
    D.scalar 2 (Fin 1) stable (assembly A c) =
      D.scalar 2 (Fin 1) stable (assembly A c') := by
  rw [scalar_assembly D A hfund, scalar_assembly D A hfund]
  exact Finset.sum_congr rfl (fun p _ ↦ h00 p)

end AxiomaticGWTest.GKM.AdmcyclesHodgeStrataNormalization
