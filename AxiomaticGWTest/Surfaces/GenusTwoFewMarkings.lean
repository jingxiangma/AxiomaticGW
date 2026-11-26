import AxiomaticGW.Surfaces.GenusTwoFewMarkings
import AxiomaticGW.Surfaces.PlaneGenusTwoFewMarkings

open AxiomaticGW SurfaceGenusTwo

-- The general domain agrees with the already certified, smaller plane frame.
example : fewMarkingQueries .plane = BelorousskiPandharipande.planeFewMarkingQueries := by
  ext q
  rw [mem_fewMarkingQueries_iff, BelorousskiPandharipande.mem_planeFewMarkingQueries_iff]
  rfl

-- The exceptional curve and a fiber retain different classes and powers.
example : FewMarkingQuery (⟨2, ![1, 0], [⟨.exceptional 0, 2⟩]⟩ :
    SurfaceQuery .hirzebruchOne) := by
  unfold FewMarkingQuery
  decide +kernel

example : FewMarkingQuery (⟨2, ![0, 1], [⟨.point, 2⟩]⟩ :
    SurfaceQuery .hirzebruchOne) := by
  unfold FewMarkingQuery
  decide +kernel

-- Equal-energy exceptional classes on the two-point blowup are both required.
example : FewMarkingQuery (⟨2, ![1, 0, 0], [⟨.exceptional 0, 2⟩]⟩ :
    SurfaceQuery .blowupTwo) := by
  unfold FewMarkingQuery
  decide +kernel

example : FewMarkingQuery (⟨2, ![0, 1, 0], [⟨.exceptional 1, 2⟩]⟩ :
    SurfaceQuery .blowupTwo) := by
  unfold FewMarkingQuery
  decide +kernel

-- The maximal allowed psi power occurs and must not be lost to the plane bound.
example : FewMarkingQuery (⟨2, ![4, 0], [⟨.unit, 0⟩, ⟨.unit, 7⟩]⟩ :
    SurfaceQuery .hirzebruchOne) := by
  unfold FewMarkingQuery
  decide +kernel

-- The few-marking suite excludes class zero even though genus two is stable.
example : ¬ FewMarkingQuery (⟨2, 0, [⟨.unit, 2⟩]⟩ :
    SurfaceQuery .blowupTwo) := by
  unfold FewMarkingQuery
  decide +kernel
