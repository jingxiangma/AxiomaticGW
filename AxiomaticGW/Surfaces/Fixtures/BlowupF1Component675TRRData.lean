module
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsData

@[expose] public section
set_option maxRecDepth 65536

namespace AxiomaticGW.Component675TRR
open BlowupF1CertifiedPoints (rational elliptic)
abbrev X := SurfaceTarget.hirzebruchOne
abbrev q := BlowupF1CompleteHComponents.key675
theorem hg : q.genus = 1 := by decide +kernel
theorem hp : ¬q.IsPrimary := by decide +kernel
def terms := PsiBoundaryExpansion.genusOneTerms (SurfaceGenusOne.extraCount q)
def termValue (t : ℚ × GluingExpression 1 (ExtraMarkings (SurfaceGenusOne.extraCount q)
    (Fin 1))) : ℚ :=
  t.1 * t.2.surfaceEval X
    (fun g S _ h beta k a ↦
      let r := SurfaceAncestorKey.ofLabels g S h beta k a
      if r.genus = 0 then SurfaceLowGenusPointCache.rationalValue X rational r
      else SurfaceLowGenusPointCache.ellipticFuel X rational elliptic 0 r)
    q.beta (SurfaceGenusOne.lowerAncestorPowers q hg hp)
    (q.orderedLabels ∘ SurfaceGenusOne.ancestorFrame q hg hp)
theorem terms_length : terms.length = 32 := by decide +kernel

def part (i : Fin 32) : ℚ := termValue (terms.get (Fin.cast terms_length.symm i))

def claimed (_i : Fin 32) : ℚ :=
  0

end AxiomaticGW.Component675TRR
