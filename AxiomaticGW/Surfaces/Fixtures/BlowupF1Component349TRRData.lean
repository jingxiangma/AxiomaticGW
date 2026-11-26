module
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsData

@[expose] public section
set_option maxRecDepth 65536

namespace AxiomaticGW.Component349TRR
open BlowupF1CertifiedPoints (rational elliptic)
abbrev X := SurfaceTarget.hirzebruchOne
abbrev q := BlowupF1CompleteHComponents.key349
theorem hg : q.genus = 0 := by decide +kernel
theorem hp : ¬q.IsPrimary := by decide +kernel
def terms := PsiBoundaryExpansion.genusZeroTerms 0 (SurfaceGenusZero.extraCount q)
def termValue (t : ℚ × GluingExpression 0 (ExtraMarkings (SurfaceGenusZero.extraCount q)
    (Fin 3))) : ℚ :=
  t.1 * t.2.surfaceEval X
    (fun g S _ h beta k a ↦ SurfaceLowGenusPointCache.rationalFuel X rational 0
      (SurfaceAncestorKey.ofLabels g S h beta k a))
    q.beta (SurfaceGenusZero.lowerAncestorPowers q hg hp)
    (q.orderedLabels ∘ SurfaceGenusZero.ancestorFrame q hg hp)
theorem terms_length : terms.length = 31 := by decide +kernel

def part (i : Fin 31) : ℚ := termValue (terms.get (Fin.cast terms_length.symm i))

def claimed (_i : Fin 31) : ℚ :=
  0

end AxiomaticGW.Component349TRR
