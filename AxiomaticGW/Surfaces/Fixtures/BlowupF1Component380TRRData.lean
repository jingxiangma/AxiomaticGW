module
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsData

@[expose] public section
set_option maxRecDepth 65536

namespace AxiomaticGW.Component380TRR
open BlowupF1CertifiedPoints (rational elliptic)
abbrev X := SurfaceTarget.hirzebruchOne
abbrev q := BlowupF1CompleteHComponents.key380
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

def claimed (i : Fin 31) : ℚ :=
  if i.val = 1 then (-1) else
  if i.val = 3 then 1 else
  if i.val = 5 then 1 else
  if i.val = 7 then (-1) else
  if i.val = 9 then 1 else
  if i.val = 11 then (-1) else
  if i.val = 13 then (-1) else
  if i.val = 15 then 1 else
  if i.val = 17 then (-1) else
  if i.val = 19 then 1 else
  if i.val = 21 then 1 else
  if i.val = 23 then (-1) else
  if i.val = 25 then (-1) else
  if i.val = 27 then 1 else
  if i.val = 29 then (-1) else
  if i.val = 30 then 1 else
  0

end AxiomaticGW.Component380TRR
