/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPrimaryPoints

/-!
# The exceptional rational complement of the shifted hyperplane row

The two rational triples in the surviving shifted-H terms carry three copies
of the selected exceptional divisor and a unit at the genus-two attachment.
Their complete contraction at the exceptional curve is minus one. The proof
retains both ordered class splittings and all inverse-metric states.

This is an exact finite calculation on each fixed surface's exceptional
generator, using the existing reconstructed genus-zero values. It supplies no
new invariant seed and makes no restriction on the requested genus-two class.
The arbitrary coefficient variable does not affect these primary rational
components. The remaining genus-two contribution is handled separately.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupExceptionalComplement
open SurfaceGenusTwo GluingExpression

/-- The actual rational pair has value minus one at every exceptional generator.
All metric signs and ordered effective splittings are checked in the kernel. -/
theorem exceptional_pair_primary (X : SurfaceTarget) (i : Fin X.blowups)
    (v : SurfacePolynomialReduction.Variable X) :
    (GetzlerGraphs.join (m := 2) (n := 2) 2 1
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) (![0, 0, 0], ![0, 0, 0])
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3)))
      (X.exceptionalCurve i) 0 ![.exceptional i, .exceptional i, .exceptional i, .unit] =
      -1 := by
  have hd : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by
    ext j
    fin_cases j <;> rfl
  simp only [GetzlerGraphs.join, pointContraction, primaryPointVertex, hd,
    and_self, ite_true]
  cases X with
  | plane => exact Fin.elim0 i
  | hirzebruchOne => fin_cases i; decide +kernel
  | blowupTwo => fin_cases i <;> decide +kernel

/-- At a different exceptional generator the same full rational pair vanishes.
The two exceptional coordinates are never identified by their equal energy. -/
theorem exceptional_pair_primary_at_generator (X : SurfaceTarget)
    (i j : Fin X.blowups) (v : SurfacePolynomialReduction.Variable X) :
    (GetzlerGraphs.join (m := 2) (n := 2) 2 1
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) (![0, 0, 0], ![0, 0, 0])
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3)))
      (X.exceptionalCurve j) 0 ![.exceptional i, .exceptional i, .exceptional i, .unit] =
      if i = j then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact exceptional_pair_primary X i v
  · rw [if_neg hij]
    have hd : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by
      ext s
      fin_cases s <;> rfl
    simp only [GetzlerGraphs.join, pointContraction, primaryPointVertex, hd,
      and_self, ite_true]
    cases X with
    | plane => exact Fin.elim0 i
    | hirzebruchOne =>
      fin_cases i
      fin_cases j
      exact (hij rfl).elim
    | blowupTwo =>
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · decide +kernel
      · decide +kernel
      · exact (hij rfl).elim

end AxiomaticGW.SurfaceGenusTwoBlowupExceptionalComplement
