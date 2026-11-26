module

public import AxiomaticGW.GKM.EquivariantCoefficients
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberOneMarking

/-! # Localization of the four one-marked genus-two fiber descendants on F₁

Report SHA256: c21c669815af64ea6336355a87aba7f5a1159433f18a3a4376623457e60883bf
-/

@[expose] public section

namespace AxiomaticGW.GKM.F1FiberOneMarking
open EquivariantCoefficients

/-- Incoming effective classes and ordered descendants. -/
def requests : Fin 4 → SurfaceQuery .hirzebruchOne :=
  ![⟨2, ![0, 1], [⟨.unit, 4⟩]⟩,
    ⟨2, ![0, 1], [⟨.hyperplane, 3⟩]⟩,
    ⟨2, ![0, 1], [⟨.exceptional 0, 3⟩]⟩,
    ⟨2, ![0, 1], [⟨.point, 2⟩]⟩]

namespace FractionTable

noncomputable section

/-- Sparse polynomial numerators in the two torus characters. -/
def numerators (i : Fin 4) : Polynomial :=
  (#[(MvPolynomial.C ((-1/120) : ℚ)),
    (MvPolynomial.C ((-7/960) : ℚ)),
    (MvPolynomial.C ((-23/2880) : ℚ)),
    (MvPolynomial.C ((1/240) : ℚ))] : Array (Polynomial))[i.val]'i.isLt

/-- Sparse polynomial denominators in the two torus characters. -/
def denominators (_ : Fin 4) : Polynomial :=
  (MvPolynomial.C (1 : ℚ))

/-- Ordinary rational constants attached to the dictionary entries. -/
def constants (i : Fin 4) : ℚ :=
  (#[(-1 / 120), (-7 / 960), (-23 / 2880), (1 / 240)] : Array (ℚ))[i.val]'i.isLt

/-- The exact quotient of the two incoming polynomials. -/
def fraction (i : Fin 4) : Coefficient :=
  embed (numerators i) / embed (denominators i)

/-- The actual denominator of every reported entry is regular at zero. -/
theorem regular (i : Fin 4) : atZero (denominators i) ≠ 0 := by
  fin_cases i <;> norm_num [denominators, atZero, map_zero, map_one, map_add, map_mul, map_pow,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]

/-- Specialization uses the literal numerator and denominator of each entry. -/
theorem specializes (i : Fin 4) : Specializes (fraction i) (constants i) := by
  refine ⟨numerators i, denominators i, regular i, rfl, ?_⟩
  fin_cases i <;> norm_num [numerators, denominators, constants, atZero, map_zero, map_one,
    map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    RingHom.id_apply, Pi.zero_apply]

/-- Cancellation in the full fraction field gives the indicated constant. -/
theorem fraction_eq_constant (i : Fin 4) :
    fraction i = (constants i : Coefficient) := by
  apply (div_eq_iff (embed_ne_zero_of_atZero _ (regular i))).mpr
  fin_cases i <;>
    norm_num [numerators, denominators, constants, map_add, map_mul, map_pow, embed_C]

end

end FractionTable

/-- The incoming ordinary values, in the held order. -/
abbrev values := FractionTable.constants

/-- The full reported two-character functions in the same order. -/
noncomputable abbrev equivariant := FractionTable.fraction

/-- Equality holds in the full two-character fraction field. -/
theorem equivariant_eq_ordinary (j : Fin 4) :
    equivariant j = (values j : Coefficient) := FractionTable.fraction_eq_constant j

/-- Regular specialization at zero yields each ordinary value. -/
theorem specializes (j : Fin 4) : Specializes (equivariant j) (values j) :=
  FractionTable.specializes j

/-- The original reconstructed descendant and native localization agree. -/
theorem accepted (j : Fin 4) : SurfaceGenusTwoBlowupDescendants.queryValue? 0
    (requests j) = some (values j) := by
  have hq : requests j = BlowupF1FiberOneMarking.requests j := by
    fin_cases j <;> decide +kernel
  rw [hq, BlowupF1FiberOneMarking.accepted]
  fin_cases j <;> decide +kernel

end AxiomaticGW.GKM.F1FiberOneMarking
