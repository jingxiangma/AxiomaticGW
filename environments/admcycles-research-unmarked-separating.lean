import AxiomaticGW.Tautological.Fixtures.AdmcyclesGenusTwo

namespace AxiomaticGW.Research.UnmarkedGenusTwo_8fbd92f6db1cf72433cc
open RelationCertificate AdmcyclesGenusTwo

/-- Requested coordinates in the fixed raw monomial-kappa graph order. -/
def target : Coordinates 8 := ![0, 0, 1, -1, 0, 0, 0, 0]

/-- Row weights found by exact linear algebra on the seven admcycles rows. -/
def witness : Certificate 7 := ⟨![0, 0, 0, (1 / 72), (-1 / 72), 0, 0]⟩

theorem accepted : check rows target witness = true := by decide +kernel

theorem in_span : interpret columns target ∈ relationSpan columns rows :=
  check_sound columns rows target witness accepted

theorem evaluated {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (ev : StrataModule 2 (Fin 0) →ₗ[ℚ] M)
    (hrows : ∀ i, ev (interpret columns (rows i)) = 0) :
    ev (interpret columns target) = 0 :=
  evaluation_eq_zero columns rows target witness accepted ev hrows

#print axioms in_span
#print axioms evaluated
end AxiomaticGW.Research.UnmarkedGenusTwo_8fbd92f6db1cf72433cc
