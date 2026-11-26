/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCanonicalQueries
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Order.RelClasses

/-!
# A reconstruction order on the full effective surface monoids

The hyperplane degree is the coefficient of `H` in the integer curve lattice.
It is nonnegative on the chosen effective generators, whereas the signed
exceptional multiplicities may be negative. Adding `Eᵢ` preserves hyperplane
degree and decreases its signed multiplicity by one.

The genus-two sectors are ordered `H`, `P`, `N`, `Kᵢ`, followed by energy within
a sector. This order permits an earlier sector at `beta + Eᵢ` to precede a later
sector at `beta`, despite its larger energy. The full class and exceptional
label are retained; the measure need not distinguish every pair of states.

These are termination and coordinate facts. They do not assert that every
residual variable of a normalized BP/L24 equation decreases in this order.
In particular, degree-zero remainders can contain several exceptional
generators, and energy-one shifted remainders need not give a strict decrease.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceTarget

/-- Hyperplane degree, evaluated at the final effective generator coordinate. -/
def planeDegree (X : SurfaceTarget) : X.Curve →+ ℕ :=
  Pi.evalAddMonoidHom (fun _ : Fin (X.blowups + 1) ↦ ℕ) (Fin.last X.blowups)

/-- The signed multiplicity in `beta = d H - ∑ alphaᵢ Eᵢ`; it is not truncated. -/
def signedMultiplicity (X : SurfaceTarget) (beta : X.Curve) (i : Fin X.blowups) : ℤ :=
  X.divisorIntersections beta i.succ

theorem planeDegree_eq_latticeCoordinates (X : SurfaceTarget) (beta : X.Curve) :
    (X.planeDegree beta : ℤ) = X.latticeCoordinates beta 0 := by
  cases X <;> rfl

/-- The outer induction degree is the actual intersection with `H`. -/
theorem planeDegree_eq_divisorIntersections (X : SurfaceTarget) (beta : X.Curve) :
    (X.planeDegree beta : ℤ) = X.divisorIntersections beta 0 := by
  rw [planeDegree_eq_latticeCoordinates, divisorIntersections, if_pos rfl]

/-- The degree-zero induction base agrees exactly with exceptional-image support. -/
theorem planeDegree_eq_zero_iff_divisorIntersections_eq_zero (X : SurfaceTarget)
    (beta : X.Curve) : X.planeDegree beta = 0 ↔ X.divisorIntersections beta 0 = 0 := by
  constructor
  · intro hd
    rw [← planeDegree_eq_divisorIntersections, hd]
    rfl
  · intro hd
    apply Int.ofNat_inj.mp
    simpa only [Nat.cast_zero] using (X.planeDegree_eq_divisorIntersections beta).trans hd

theorem signedMultiplicity_eq (X : SurfaceTarget) (beta : X.Curve)
    (i : Fin X.blowups) :
    X.signedMultiplicity beta i = (X.planeDegree beta : ℤ) - (beta i.castSucc : ℤ) := by
  cases X
  · exact i.elim0
  · fin_cases i
    change -((beta 0 : ℤ) - beta 1) = (beta 1 : ℤ) - beta 0
    omega
  · fin_cases i
    · change -((beta 0 : ℤ) - beta 2) = (beta 2 : ℤ) - beta 0
      omega
    · change -((beta 1 : ℤ) - beta 2) = (beta 2 : ℤ) - beta 1
      omega

theorem planeDegree_exceptionalCurve (X : SurfaceTarget) (i : Fin X.blowups) :
    X.planeDegree (X.exceptionalCurve i) = 0 := by
  cases X <;> fin_cases i <;> rfl

theorem planeDegree_lineCurve (X : SurfaceTarget) :
    X.planeDegree X.lineCurve = 1 := rfl

/-- Degree zero includes arbitrary sums of all exceptional generators, rather than
only the exceptional divisor used to shift a particular equation. -/
theorem eq_sum_exceptionalCurve_of_planeDegree_eq_zero (X : SurfaceTarget)
    (beta : X.Curve) (hd : X.planeDegree beta = 0) :
    beta = ∑ i : Fin X.blowups, beta i.castSucc • X.exceptionalCurve i := by
  nth_rw 1 [pi_eq_sum_univ' beta]
  rw [Fin.sum_univ_castSucc]
  have hz : beta (Fin.last X.blowups) = 0 := hd
  simp only [hz, zero_nsmul, add_zero, exceptionalCurve]

theorem energy_exceptionalCurve (X : SurfaceTarget) (i : Fin X.blowups) :
    X.effective.energy (X.exceptionalCurve i) = 1 := by
  exact Int.ofNat_inj.mp (X.c1Degree_exceptionalCurve i)

theorem signedMultiplicity_add (X : SurfaceTarget) (beta gamma : X.Curve)
    (i : Fin X.blowups) :
    X.signedMultiplicity (beta + gamma) i =
      X.signedMultiplicity beta i + X.signedMultiplicity gamma i := by
  rw [signedMultiplicity_eq, signedMultiplicity_eq, signedMultiplicity_eq, map_add]
  simp only [Pi.add_apply, Nat.cast_add]
  ring

theorem planeDegree_add_exceptionalCurve (X : SurfaceTarget) (beta : X.Curve)
    (i : Fin X.blowups) :
    X.planeDegree (beta + X.exceptionalCurve i) = X.planeDegree beta := by
  rw [map_add, planeDegree_exceptionalCurve, add_zero]

theorem energy_add_exceptionalCurve (X : SurfaceTarget) (beta : X.Curve)
    (i : Fin X.blowups) :
    X.effective.energy (beta + X.exceptionalCurve i) = X.effective.energy beta + 1 := by
  rw [map_add, energy_exceptionalCurve]

/-- A shift subtracts one from its own signed multiplicity and preserves the others. -/
theorem signedMultiplicity_add_exceptionalCurve (X : SurfaceTarget) (beta : X.Curve)
    (i j : Fin X.blowups) :
    X.signedMultiplicity (beta + X.exceptionalCurve j) i =
      X.signedMultiplicity beta i - if i = j then 1 else 0 := by
  rw [signedMultiplicity_add]
  have he : X.signedMultiplicity (X.exceptionalCurve j) i =
      -(if i = j then 1 else 0 : ℤ) := by
    cases X <;> fin_cases i <;> fin_cases j <;> decide +kernel
  rw [he, sub_eq_add_neg]

/-- The last coordinate is monotone under an effective additive splitting. -/
theorem planeDegree_le_of_add_eq (X : SurfaceTarget) {beta gamma delta : X.Curve}
    (h : gamma + delta = beta) : X.planeDegree gamma ≤ X.planeDegree beta := by
  have hd := congrArg X.planeDegree h
  rw [map_add] at hd
  omega

/-- A nonzero effective remainder strictly lowers the positive energy. -/
theorem energy_lt_of_add_eq (X : SurfaceTarget) {beta gamma delta : X.Curve}
    (h : gamma + delta = beta) (hdelta : delta ≠ 0) :
    X.effective.energy gamma < X.effective.energy beta := by
  have he := congrArg X.effective.energy h
  rw [map_add] at he
  have hd : 0 < X.effective.energy delta := Nat.pos_of_ne_zero
    (fun hz ↦ hdelta ((X.effective.energy_eq_zero_iff delta).mp hz))
  omega

/-- Every effective subclass of a shifted source has at most the original plane degree. -/
theorem planeDegree_le_of_shifted_add_eq (X : SurfaceTarget) (i : Fin X.blowups)
    {beta gamma delta : X.Curve} (h : gamma + delta = beta + X.exceptionalCurve i) :
    X.planeDegree gamma ≤ X.planeDegree beta := by
  have hd := X.planeDegree_le_of_add_eq h
  rwa [planeDegree_add_exceptionalCurve] at hd

/-- A shifted splitting strictly lowers plane degree exactly when its remainder has
positive plane degree. This allows arbitrary degree-zero exceptional combinations. -/
theorem planeDegree_lt_of_shifted_add_eq_iff (X : SurfaceTarget) (i : Fin X.blowups)
    {beta gamma delta : X.Curve} (h : gamma + delta = beta + X.exceptionalCurve i) :
    X.planeDegree gamma < X.planeDegree beta ↔ 0 < X.planeDegree delta := by
  have hd := congrArg X.planeDegree h
  rw [map_add, planeDegree_add_exceptionalCurve] at hd
  omega

/-- Equal plane degree in a shifted splitting means precisely a degree-zero remainder. -/
theorem planeDegree_eq_of_shifted_add_eq_iff (X : SurfaceTarget) (i : Fin X.blowups)
    {beta gamma delta : X.Curve} (h : gamma + delta = beta + X.exceptionalCurve i) :
    X.planeDegree gamma = X.planeDegree beta ↔ X.planeDegree delta = 0 := by
  have hd := congrArg X.planeDegree h
  rw [map_add, planeDegree_add_exceptionalCurve] at hd
  omega

/-- Shifted same-sector energy decreases precisely beyond the energy-one remainder. -/
theorem energy_lt_of_shifted_add_eq_iff (X : SurfaceTarget) (i : Fin X.blowups)
    {beta gamma delta : X.Curve} (h : gamma + delta = beta + X.exceptionalCurve i) :
    X.effective.energy gamma < X.effective.energy beta ↔ 1 < X.effective.energy delta := by
  have he := congrArg X.effective.energy h
  rw [map_add, energy_add_exceptionalCurve] at he
  omega

/-- A zero-plane-degree remainder of energy one is exactly one exceptional
generator. Full coordinates distinguish the two exceptional curves. -/
theorem eq_exceptionalCurve_of_energy_one_of_planeDegree_zero (X : SurfaceTarget) (delta : X.Curve)
    (he : X.effective.energy delta = 1) (hd : X.planeDegree delta = 0) :
    ∃ j : Fin X.blowups, delta = X.exceptionalCurve j := by
  cases X
  · change (∑ k : Fin 1, (![3] : Fin 1 → ℕ) k * delta k) = 1 at he
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at he
    omega
  · change delta 1 = 0 at hd
    change (∑ k : Fin 2, (![1, 2] : Fin 2 → ℕ) k * delta k) = 1 at he
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Nat.one_mul] at he
    have h0 : delta 0 = 1 := by omega
    refine ⟨0, ?_⟩
    ext k
    fin_cases k
    · change delta 0 = 1
      exact h0
    · change delta 1 = 0
      exact hd
  · change delta 2 = 0 at hd
    change (∑ k : Fin 3, (![1, 1, 1] : Fin 3 → ℕ) k * delta k) = 1 at he
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Nat.one_mul] at he
    change delta 0 + delta 1 + 1 * delta 2 = 1 at he
    rw [Nat.one_mul] at he
    have hh : delta 0 = 1 ∨ delta 1 = 1 := by omega
    rcases hh with h0 | h1
    · refine ⟨0, ?_⟩
      ext k
      fin_cases k
      · change delta 0 = 1
        exact h0
      · change delta 1 = 0
        omega
      · change delta 2 = 0
        exact hd
    · refine ⟨1, ?_⟩
      ext k
      fin_cases k
      · change delta 0 = 0
        omega
      · change delta 1 = 1
        exact h1
      · change delta 2 = 0
        exact hd


/-- A shifted split preserving both plane degree and energy has a single
exceptional generator as its remainder, which need not be the chosen shift. -/
theorem exceptional_remainder_of_shifted_same_planeDegree_and_energy
    (X : SurfaceTarget) (i : Fin X.blowups) {beta gamma delta : X.Curve}
    (h : gamma + delta = beta + X.exceptionalCurve i)
    (hd : X.planeDegree gamma = X.planeDegree beta)
    (he : X.effective.energy gamma = X.effective.energy beta) :
    ∃ j : Fin X.blowups, delta = X.exceptionalCurve j := by
  have hdeltad : X.planeDegree delta = 0 :=
    (X.planeDegree_eq_of_shifted_add_eq_iff i h).mp hd
  have hdeltae := congrArg X.effective.energy h
  rw [map_add, energy_add_exceptionalCurve, he] at hdeltae
  exact X.eq_exceptionalCurve_of_energy_one_of_planeDegree_zero delta
    (by omega) hdeltad

end SurfaceTarget

namespace SurfaceGenusTwoBlowupOrder

/-- Canonical genus-two sectors. Every actual exceptional divisor retains its own label. -/
inductive Family (X : SurfaceTarget)
  | hyperplane
  | point
  | primary
  | exceptional (i : Fin X.blowups)

/-- The source reconstruction sector order `H`, `P`, `N`, `Kᵢ`. -/
def Family.rank {X : SurfaceTarget} : Family X → ℕ
  | .hyperplane => 0
  | .point => 1
  | .primary => 2
  | .exceptional _ => 3

/-- The existing canonical query represented by a sector and its full effective class.
The point sector is dimension compatible only at positive energy. -/
def Family.query {X : SurfaceTarget} (f : Family X) (beta : X.Curve) : SurfaceQuery X :=
  match f with
  | .hyperplane => SurfaceFirstDescendant.query 2 beta .hyperplane (X.effective.energy beta)
  | .point => SurfaceFirstDescendant.query 2 beta .point (X.effective.energy beta - 1)
  | .primary => SurfaceQuery.points X 2 beta (X.effective.energy beta + 1)
  | .exceptional i =>
      SurfaceFirstDescendant.query 2 beta (.exceptional i) (X.effective.energy beta)

theorem Family.query_mem_canonicalQueries {X : SurfaceTarget} (f : Family X) (beta : X.Curve)
    (hp : f = .point → 0 < X.effective.energy beta) :
    f.query beta ∈ SurfaceGenusTwo.canonicalQueries X beta := by
  rw [SurfaceGenusTwo.mem_canonicalQueries]
  cases f
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr ⟨hp rfl, rfl⟩))
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))

/-- Every canonical query retains a corresponding order sector and its original class. -/
theorem family_of_mem_canonicalQueries {X : SurfaceTarget} {beta : X.Curve}
    {q : SurfaceQuery X} (hq : q ∈ SurfaceGenusTwo.canonicalQueries X beta) :
    ∃ f : Family X, f.query beta = q := by
  rcases (SurfaceGenusTwo.mem_canonicalQueries beta q).mp hq with
    h | h | ⟨i, h⟩ | ⟨_, h⟩
  · exact ⟨.primary, h.symm⟩
  · exact ⟨.hyperplane, h.symm⟩
  · exact ⟨.exceptional i, h.symm⟩
  · exact ⟨.point, h.symm⟩

/-- The state retains full curve coordinates and the particular exceptional sector. -/
abbrev State (X : SurfaceTarget) := X.Curve × Family X

/-- Plane degree is the outer induction; sectors precede energy in the inner induction. -/
def measure (X : SurfaceTarget) (s : State X) : ℕ × (ℕ × ℕ) :=
  (X.planeDegree s.1, s.2.rank, X.effective.energy s.1)

/-- Strict lexicographic decrease in plane degree, sector, and energy. -/
def Earlier (X : SurfaceTarget) : State X → State X → Prop :=
  InvImage (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) (measure X)

theorem earlier_iff (X : SurfaceTarget) (s t : State X) : Earlier X s t ↔
    X.planeDegree s.1 < X.planeDegree t.1 ∨
      (X.planeDegree s.1 = X.planeDegree t.1 ∧
        (s.2.rank < t.2.rank ∨
          (s.2.rank = t.2.rank ∧ X.effective.energy s.1 < X.effective.energy t.1))) := by
  rw [Earlier, InvImage, Prod.lex_def, Prod.lex_def]
  rfl

/-- Full effective classes, including arbitrary exceptional multiples, support this induction. -/
theorem earlier_wellFounded (X : SurfaceTarget) : WellFounded (Earlier X) :=
  InvImage.wf (measure X)
    (Nat.lt_wfRel.wf.prod_lex (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf))

theorem earlier_of_planeDegree_lt (X : SurfaceTarget) (s t : State X)
    (h : X.planeDegree s.1 < X.planeDegree t.1) : Earlier X s t :=
  (earlier_iff X s t).mpr (Or.inl h)

/-- Earlier sectors can use classes of larger energy at the same plane degree. -/
theorem earlier_of_rank_lt (X : SurfaceTarget) (s t : State X)
    (hd : X.planeDegree s.1 ≤ X.planeDegree t.1) (hf : s.2.rank < t.2.rank) :
    Earlier X s t := by
  rcases Nat.lt_or_eq_of_le hd with hd | hd
  · exact earlier_of_planeDegree_lt X s t hd
  · exact (earlier_iff X s t).mpr (Or.inr ⟨hd, Or.inl hf⟩)

theorem earlier_of_energy_lt (X : SurfaceTarget) (s t : State X)
    (hd : X.planeDegree s.1 ≤ X.planeDegree t.1) (hf : s.2.rank = t.2.rank)
    (he : X.effective.energy s.1 < X.effective.energy t.1) : Earlier X s t := by
  rcases Nat.lt_or_eq_of_le hd with hd | hd
  · exact earlier_of_planeDegree_lt X s t hd
  · exact (earlier_iff X s t).mpr (Or.inr ⟨hd, Or.inr ⟨hf, he⟩⟩)

/-- A proper effective subclass always precedes its source in the same sector. -/
theorem earlier_of_effective_subclass (X : SurfaceTarget) (f : Family X)
    {beta gamma delta : X.Curve} (h : gamma + delta = beta) (hdelta : delta ≠ 0) :
    Earlier X (gamma, f) (beta, f) :=
  earlier_of_energy_lt X (gamma, f) (beta, f)
    (X.planeDegree_le_of_add_eq h) rfl (X.energy_lt_of_add_eq h hdelta)

/-- Every effective subclass of a shifted source precedes a later original-class sector. -/
theorem earlier_of_shifted_subclass_rank_lt (X : SurfaceTarget) (i : Fin X.blowups)
    (f g : Family X) {beta gamma delta : X.Curve}
    (h : gamma + delta = beta + X.exceptionalCurve i) (hf : f.rank < g.rank) :
    Earlier X (gamma, f) (beta, g) :=
  earlier_of_rank_lt X (gamma, f) (beta, g)
    (X.planeDegree_le_of_shifted_add_eq i h) hf

/-- Exact same-sector decrease criterion for an effective splitting of a shifted source.
A zero- or energy-one exceptional remainder is not covered by termination alone. -/
theorem earlier_shifted_same_family_iff (X : SurfaceTarget) (i : Fin X.blowups)
    (f : Family X) {beta gamma delta : X.Curve}
    (h : gamma + delta = beta + X.exceptionalCurve i) :
    Earlier X (gamma, f) (beta, f) ↔
      0 < X.planeDegree delta ∨ 1 < X.effective.energy delta := by
  rw [earlier_iff]
  simp only [Nat.lt_irrefl, false_or, true_and]
  have hd := congrArg X.planeDegree h
  rw [map_add, SurfaceTarget.planeDegree_add_exceptionalCurve] at hd
  have he := congrArg X.effective.energy h
  rw [map_add, SurfaceTarget.energy_add_exceptionalCurve] at he
  omega

/-- For the same sector, shifted tails of energy at least two suffice for decrease.
Energy-one tails require the actual equation and full-class coefficients to be examined. -/
theorem earlier_of_shifted_subclass_energy_lt (X : SurfaceTarget) (i : Fin X.blowups)
    (f : Family X) {beta gamma delta : X.Curve}
    (h : gamma + delta = beta + X.exceptionalCurve i)
    (he : 1 < X.effective.energy delta) : Earlier X (gamma, f) (beta, f) :=
  earlier_of_energy_lt X (gamma, f) (beta, f)
    (X.planeDegree_le_of_shifted_add_eq i h) rfl
    ((X.energy_lt_of_shifted_add_eq_iff i h).mpr he)

end SurfaceGenusTwoBlowupOrder

end AxiomaticGW
