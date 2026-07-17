/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.Constant
public import AxiomaticGW.CohFT.TopologicalPart

/-!
# Classification of topological CohFTs

Every scalar-valued topological CohFT is the stable restriction of the
canonical theory of the commutative Frobenius algebra extracted from its
three-point correlator.
-/

@[expose] public section

namespace AxiomaticGW

namespace TopologicalCohFT

variable {R V : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]

omit [Algebra ℚ R] [Module.Free R V] [Module.Finite R V] in
private theorem pairing_eq_of_form_eq
    {P Q : SymmetricPerfectPairing R V} (h : P.form = Q.form) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

omit [Algebra ℚ R] in
private theorem genusZero_omega_eq (T U : TopologicalCohFT R V)
    (hpairing : T.pairing = U.pairing)
    (hthree : T.omega 0 (Fin 3) StableArity.zero_fin_three =
      U.omega 0 (Fin 3) StableArity.zero_fin_three)
    (S : Type) [Fintype S] (h : StableArity 0 S) :
    T.omega 0 S h = U.omega 0 S h := by
  induction hn : Fintype.card S using Nat.strong_induction_on generalizing S with
  | h n ih =>
      have hn3 : 3 ≤ n := by
        simpa [StableArity, hn] using h
      rcases hn3.eq_or_lt with rfl | hn3
      · let e : Fin 3 ≃ S := (Fintype.equivFinOfCardEq hn).symm
        calc
          T.omega 0 S h =
              (T.omega 0 (Fin 3) StableArity.zero_fin_three).domDomCongr e :=
            (T.relabel 0 (Fin 3) S StableArity.zero_fin_three h e).symm
          _ = (U.omega 0 (Fin 3) StableArity.zero_fin_three).domDomCongr e :=
            congrArg (fun f ↦ f.domDomCongr e) hthree
          _ = U.omega 0 S h :=
            U.relabel 0 (Fin 3) S StableArity.zero_fin_three h e
      · have hn4 : 4 ≤ n := by omega
        have hright : StableArity 0 (Option (Fin (n - 2))) := by
          simp [StableArity]
          omega
        have hleft_eq :
            T.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two =
              U.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two :=
          ih 3 (by omega) (Option (Fin 2))
            StableArity.zero_option_fin_two (by simp)
        have hright_lt : Fintype.card (Option (Fin (n - 2))) < n := by
          simp
          omega
        have hright_eq : T.omega 0 (Option (Fin (n - 2))) hright =
            U.omega 0 (Option (Fin (n - 2))) hright :=
          ih _ hright_lt (Option (Fin (n - 2))) hright rfl
        let hsum := StableArity.separating
          StableArity.zero_option_fin_two hright
        have hsum_eq : T.omega 0 (Fin 2 ⊕ Fin (n - 2)) hsum =
            U.omega 0 (Fin 2 ⊕ Fin (n - 2)) hsum := by
          calc
            T.omega 0 (Fin 2 ⊕ Fin (n - 2)) hsum =
                T.pairing.pairContract
                  (T.omega 0 (Option (Fin 2))
                    StableArity.zero_option_fin_two)
                  (T.omega 0 (Option (Fin (n - 2))) hright) :=
              (T.separating 0 0 (Fin 2) (Fin (n - 2))
                StableArity.zero_option_fin_two hright).symm
            _ = U.pairing.pairContract
                  (U.omega 0 (Option (Fin 2))
                    StableArity.zero_option_fin_two)
                  (U.omega 0 (Option (Fin (n - 2))) hright) := by
              rw [hpairing, hleft_eq, hright_eq]
            _ = U.omega 0 (Fin 2 ⊕ Fin (n - 2)) hsum :=
              U.separating 0 0 (Fin 2) (Fin (n - 2))
                StableArity.zero_option_fin_two hright
        have hcard : 2 + (n - 2) = n := by omega
        let e : Fin 2 ⊕ Fin (n - 2) ≃ S :=
          finSumFinEquiv.trans
            ((finCongr hcard).trans (Fintype.equivFinOfCardEq hn).symm)
        calc
          T.omega 0 S h =
              (T.omega 0 (Fin 2 ⊕ Fin (n - 2)) hsum).domDomCongr e :=
            (T.relabel 0 (Fin 2 ⊕ Fin (n - 2)) S hsum h e).symm
          _ = (U.omega 0 (Fin 2 ⊕ Fin (n - 2)) hsum).domDomCongr e :=
            congrArg (fun f ↦ f.domDomCongr e) hsum_eq
          _ = U.omega 0 S h :=
            U.relabel 0 (Fin 2 ⊕ Fin (n - 2)) S hsum h e

omit [Algebra ℚ R] in
private theorem omega_eq (T U : TopologicalCohFT R V)
    (hpairing : T.pairing = U.pairing)
    (hthree : T.omega 0 (Fin 3) StableArity.zero_fin_three =
      U.omega 0 (Fin 3) StableArity.zero_fin_three)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) :
    T.omega g S h = U.omega g S h := by
  induction g generalizing S with
  | zero => exact genusZero_omega_eq T U hpairing hthree S h
  | succ g ih =>
      have h' : StableArity (g + 1) S := by
        simpa [Nat.succ_eq_add_one] using h
      calc
        T.omega (Nat.succ g) S h = T.pairing.selfContract
            (T.omega g (S ⊕ Fin 2) (StableArity.sum_fin_two_iff.mpr h')) := by
          simpa [Nat.succ_eq_add_one] using (T.nonseparating g S h').symm
        _ = U.pairing.selfContract
            (U.omega g (S ⊕ Fin 2) (StableArity.sum_fin_two_iff.mpr h')) := by
          rw [hpairing]
          exact congrArg U.pairing.selfContract
            (ih (S ⊕ Fin 2) (StableArity.sum_fin_two_iff.mpr h'))
        _ = U.omega (Nat.succ g) S h := by
          simpa [Nat.succ_eq_add_one] using U.nonseparating g S h'

/-- Extract the commutative Frobenius algebra classified by a topological
CohFT. A separate carrier records which theory supplied the multiplication. -/
noncomputable def toCommFrobeniusAlgebra (T : TopologicalCohFT R V) :=
  T.toConstantCohFT.toGenusZeroCohFT.toCommFrobeniusAlgebra
    (constantStableCurveCohomology.genusZeroGeometry R)

/-- Degree-zero scalarization of the constant CohFT model recovers the
original topological correlators. -/
@[simp]
theorem toConstantCohFT_topologicalPart_omega
    (T : TopologicalCohFT R V) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) :
    (T.toConstantCohFT.topologicalPart
      (constantStableCurveCohomology.connectedDegreeZero R)).omega g S h =
      T.omega g S h := by
  ext a
  change ↑((DirectSum.decompose (constantDegree R) (T.omega g S h a)) 0) =
    T.omega g S h a
  exact DirectSum.decompose_of_mem_same (constantDegree R)
    (by simp [constantDegree])

/-- Classification of scalar-valued topological CohFTs: in every stable genus
and arity, the original correlator agrees with the canonical Frobenius
correlator after the identity identification of state spaces. -/
theorem classification (T : TopologicalCohFT R V) (g : ℕ)
    (S : Type) [Fintype S] (h : StableArity g S) :
    ((T.toCommFrobeniusAlgebra.toTopologicalCohFT.omega g S h).compLinearMap
      (fun _ ↦ (GenusZeroCohFT.FrobeniusCarrier.toStateSpace
        T.toConstantCohFT.toGenusZeroCohFT
        (constantStableCurveCohomology.genusZeroGeometry R)).symm.toLinearMap)) =
      T.omega g S h := by
  let G := constantStableCurveCohomology.genusZeroGeometry R
  let T₀ := T.toConstantCohFT.toGenusZeroCohFT
  let F := T₀.toCommFrobeniusAlgebra G
  let U : TopologicalCohFT R V := F.toTopologicalCohFT
  have hpairingForm : U.pairing.form = T.pairing.form := by
    ext x y
    change F.pairing.form
        ((GenusZeroCohFT.FrobeniusCarrier.toStateSpace T₀ G).symm x)
        ((GenusZeroCohFT.FrobeniusCarrier.toStateSpace T₀ G).symm y) =
      T.pairing.form x y
    rw [GenusZeroCohFT.toCommFrobeniusAlgebra_pairing]
    rfl
  have hpairing : U.pairing = T.pairing :=
    pairing_eq_of_form_eq hpairingForm
  have hthree : U.omega 0 (Fin 3) StableArity.zero_fin_three =
      T.omega 0 (Fin 3) StableArity.zero_fin_three := by
    ext a
    change F.correlator 0 (Fin 3) a = T.omega 0 (Fin 3)
      StableArity.zero_fin_three a
    rw [GenusZeroCohFT.toCommFrobeniusAlgebra_correlator_zero_fin_three]
    rfl
  change U.omega g S h = T.omega g S h
  exact omega_eq U T hpairing hthree g S h

end TopologicalCohFT

end AxiomaticGW
