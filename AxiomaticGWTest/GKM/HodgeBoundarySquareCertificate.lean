module

public import AxiomaticGW.GKM.Fixtures.HodgeBoundarySquareRealization

@[expose] public section
namespace AxiomaticGWTest.GKM.HodgeBoundarySquareCertificate
open AxiomaticGW AxiomaticGW.GKM RelationCertificate HodgeBoundarySquareRows
open HodgeBoundarySquareCertificate HodgeDegreeZeroStrataSpecialization

/-- The auxiliary kappa-two column occurs in an active original row but cancels in the target. -/
theorem auxiliary_column :
    columns 0 = TautologicalStratum.kappaGenerator 2 (Fin 1) HodgeDegreeOneRealization.stable 2 ∧
    rows 1 0 ≠ 0 ∧ witness.weights 1 ≠ 0 ∧ residual 0 = 0 := by
  exact ⟨rfl, by decide +kernel⟩

/-- Removing a shared-edge contribution fails arithmetic replay with the held witness. -/
theorem missing_excess_rejected :
    check rows ((200 : ℚ) • half - Function.update boundarySquare 11 0) witness = false := by
  decide +kernel

/-- Omitting the Hodge half-square factor changes the held relation. -/
theorem wrong_scale_rejected :
    check rows ((100 : ℚ) • half - boundarySquare) witness = false := by decide +kernel

/-- The ordinary first-blowup class equals 1/25 of the raw discriminant square
in the checked quotient. -/
theorem first_blowup_quotient :
    let proj := StrataModule.quotientMk (relationSpan columns rows)
    proj (ordinary .hirzebruchOne) = (1 / 25 : ℚ) • proj squarePacket := by
  dsimp only
  rw [ordinary, map_smul, quotient_half, smul_smul]
  norm_num [SurfaceTarget.blowups]

end AxiomaticGWTest.GKM.HodgeBoundarySquareCertificate
