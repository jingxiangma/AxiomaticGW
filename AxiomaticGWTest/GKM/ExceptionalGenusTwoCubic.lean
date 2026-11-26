module

import AxiomaticGW.GKM.Fixtures.ExceptionalCubicGeometricLoci
import AxiomaticGW.GKM.Fixtures.ExceptionalDoubleCoverChain
import AxiomaticGW.GKM.Fixtures.ExceptionalEllipticVertex

set_option linter.privateModule false
namespace AxiomaticGWTest.GKM.ExceptionalGenusTwoCubic
open AxiomaticGW.GKM EquivariantCoefficients ExceptionalGenusTwoCubicReplay

-- The primitive first exceptional edge has flag x-y and transverse character y at its source.
example : EllipticHodge.source [] (x-y) y (fun _ : Fin 1 ↦ x-y) EllipticHodge.nativeMoment =
    -1 / (24 * (x-y) * y) := ExceptionalEllipticVertex.unmarked _ _ x_sub_y_ne_zero y_ne_zero

-- Switching exceptional curves keeps the ordinary zero and changes the linear form.
example : equivariant .first ≠ equivariant .second := by
  intro h
  have hd : (240 : Coefficient) ≠ 0 := by norm_num
  change (x+y)/240 = (y-2*x)/240 at h
  have hlin := (div_left_inj' hd).mp h
  apply x_ne_zero
  linear_combination (1/3 : Coefficient) * hlin

example : (requests .second).dimensionVanishing? = some 0 ∧
    (∑ g : Fin 3, ∑ m : Fin 2, locus .second g m) = (y - 2*x) / 240 :=
  ⟨ordinary .second, sum_loci .second⟩

-- The center of the actual 1+1 chain in 2E has two outgoing flags. At (x,y)=(2,5)
-- on the first exceptional axis their weights are 3 and the transverse character is 2.
example : ExceptionalDoubleCoverChain.center [3] (3 : ℚ) 2 = -199/466560 ∧
    2^3 * ExceptionalDoubleCoverChain.center [3] (3 : ℚ) 2 / 2 = -199/116640 ∧
    ExceptionalDoubleCoverChain.center [1, 2] (3 : ℚ) 2 = 1/2916 ∧
    2^4 * ExceptionalDoubleCoverChain.center [1, 2] (3 : ℚ) 2 / 2 = 2/729 := by
  obtain ⟨cubic, pair⟩ :=
    ExceptionalDoubleCoverChain.center_eq (3 : ℚ) 2 (by norm_num) (by norm_num)
  rw [cubic, pair]
  norm_num

end AxiomaticGWTest.GKM.ExceptionalGenusTwoCubic
