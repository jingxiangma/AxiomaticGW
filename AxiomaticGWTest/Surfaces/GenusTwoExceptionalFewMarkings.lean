module

import AxiomaticGW.Surfaces.Fixtures.GenusTwoExceptionalFewMarkings

set_option linter.privateModule false
namespace AxiomaticGWTest.GenusTwoExceptionalFewMarkings
open AxiomaticGW GenusTwoExceptionalFewMarkings SurfaceGenusTwo

-- Both exceptional coordinates survive the ordered two-marking certificate.
example : TwoBlowups.requests 174 =
    (⟨2, ![1, 1, 0], [⟨.point, 2⟩, ⟨.hyperplane, 0⟩]⟩ : SurfaceQuery .blowupTwo) := by
  decide +kernel

example : exceptionalPointQueryValue? (TwoBlowups.requests 174) = some 0 :=
  (TwoBlowups.accepted 174).2

-- Neither the strict transform of the line nor a point-free exceptional query passes this test.
example : exceptionalPointQueryValue?
    (⟨2, ![0, 0, 1], [⟨.point, 1⟩]⟩ : SurfaceQuery .blowupTwo) = none ∧
    exceptionalPointQueryValue?
      (⟨2, ![1, 0, 0], [⟨.exceptional 0, 2⟩]⟩ : SurfaceQuery .blowupTwo) = none := by
  decide +kernel

end AxiomaticGWTest.GenusTwoExceptionalFewMarkings
