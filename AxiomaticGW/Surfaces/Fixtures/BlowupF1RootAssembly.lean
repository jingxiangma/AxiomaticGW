/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121OuterReplay
public import AxiomaticGW.Surfaces.ScalarPointRootParts
public import AxiomaticGW.Surfaces.GenusTwoL24FullFrame

/-!
# Finite root assembly for the fixed first F1 H constant

The request is source class (E,F) = (1,1), one added point and external labels
H,E0,E0,E0. The complete original Fin 815 frame and its relation coefficients
are unchanged. Root pieces accept any existing certified residual cache; the
point backends are the already certified F1 implementations.

The four full curve splits and two point distributions are reused from the
accepted term-121 replay. That diagnostic dependency is deliberately upward.
No new graph format, numerical seed or geometric input is introduced. The
term-121 numerical certificate is reused directly, without recomputation.
-/

@[expose] public section

namespace AxiomaticGW.BlowupF1RootAssembly

open SurfaceGenusTwo
open BlowupF1CertifiedPoints (rational elliptic rational_eq elliptic_eq)
open scoped BigOperators

abbrev X := SurfaceTarget.hirzebruchOne

def sourceCurve : X.Curve := ![1, 1]

def insertions : Fin 4 → SurfaceBasisLabel X :=
  ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0]

/-- Reuse the already checked complete ordered splitting enumeration. -/
abbrev sourceSplits := BlowupF1H121OuterParts.sourceSplits

def vertex (cache : ResidualCache X) := SurfacePointPullback.vertex X
  (constantVertexWithPointLookup X cache rational elliptic)

/-- The original coefficient and original decorated term at its original frame index. -/
def originalWeighted (j : Fin 815) : ℚ :=
  L24CorrectionsReplay.fullClaim j *
    guardedConstantPointContraction X (L24Gluing.term j) sourceCurve 1 insertions

def fundamentalPart (cache : ResidualCache X) (j : Fin 815) : ℚ :=
  L24CorrectionsReplay.fullClaim j *
    (L24Gluing.term j).expression.scalarPointRootFundamental X (vertex cache)
      (L24Gluing.term j).decoration (L24Gluing.term j).labels sourceCurve 1 insertions

def separatingPart (cache : ResidualCache X) (j : Fin 815) (i : Fin 4)
    (b : SurfaceBasisLabel X) (k : Fin 2) : ℚ :=
  L24CorrectionsReplay.fullClaim j *
    (L24Gluing.term j).expression.scalarPointRootSeparating X (vertex cache)
      (L24Gluing.term j).decoration (L24Gluing.term j).labels 1
      (sourceSplits i) b (k.val, 1 - k.val) insertions

def nonseparatingPart (cache : ResidualCache X) (j : Fin 815)
    (b : SurfaceBasisLabel X) : ℚ :=
  L24CorrectionsReplay.fullClaim j *
    (L24Gluing.term j).expression.scalarPointRootNonseparating X (vertex cache)
      (L24Gluing.term j).decoration (L24Gluing.term j).labels sourceCurve 1 b insertions

/-- All 37 envelope slots remain. A root's other sectors are structurally zero. -/
def rootSum (cache : ResidualCache X) (j : Fin 815) : ℚ :=
  fundamentalPart cache j +
    (∑ i : Fin 4, ∑ b : SurfaceBasisLabel X, ∑ k : Fin 2, separatingPart cache j i b k) +
    ∑ b : SurfaceBasisLabel X, nonseparatingPart cache j b

/-- Every lower-genus original weighted term is exactly its complete finite root sum. -/
theorem originalWeighted_eq_rootSum (cache : ResidualCache X) (j : Fin 815)
    (h : (L24Gluing.term j).expression.maxComponentGenus < 2) :
    originalWeighted j = rootSum cache j := by
  calc
    originalWeighted j = L24CorrectionsReplay.fullClaim j *
        (L24Gluing.term j).expression.scalarPointContraction X (vertex cache)
          (L24Gluing.term j).decoration (L24Gluing.term j).labels
          sourceCurve 1 insertions := by
      rw [originalWeighted,
        ← guardedConstantPointContractionWithPointLookup_eq X cache rational elliptic
          rational_eq elliptic_eq,
        guardedConstantPointContractionWithPointLookup, if_neg (not_le_of_gt h)]
      rfl
    _ = rootSum cache j := by
      rw [GluingExpression.weighted_scalarPointContraction_eq_root_parts]
      change _ +
        (∑ split ∈ X.splittings ![1, 1], ∑ b : SurfaceBasisLabel X,
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal 1,
            L24CorrectionsReplay.fullClaim j *
              (L24Gluing.term j).expression.scalarPointRootSeparating X (vertex cache)
                (L24Gluing.term j).decoration (L24Gluing.term j).labels 1 split b ij
                insertions) + _ = _
      rw [BlowupF1H121OuterParts.outer_sum_eq_indexed]
      rfl

/-- Coefficient-zero entries are retained and require no contraction evaluation. -/
theorem originalWeighted_eq_zero_of_coefficient (j : Fin 815)
    (h : L24CorrectionsReplay.fullClaim j = 0) : originalWeighted j = 0 := by
  rw [originalWeighted, h, zero_mul]

/-- The existing higher-genus guard retains its original zero-term proof. -/
theorem originalWeighted_eq_zero_of_genus_guard (j : Fin 815)
    (h : 2 ≤ (L24Gluing.term j).expression.maxComponentGenus) :
    originalWeighted j = 0 := by
  rw [originalWeighted,
    guardedConstantPointContraction_eq_zero X (L24Gluing.term j) h, mul_zero]

/-- Substitute separately checked slot values without re-evaluating a contraction. -/
theorem originalWeighted_eq_sum_claims (cache : ResidualCache X) (j : Fin 815)
    (h : (L24Gluing.term j).expression.maxComponentGenus < 2)
    (fundamental : ℚ) (separating : Fin 4 → SurfaceBasisLabel X → Fin 2 → ℚ)
    (nonseparating : SurfaceBasisLabel X → ℚ)
    (hfundamental : fundamentalPart cache j = fundamental)
    (hseparating : ∀ i b k, separatingPart cache j i b k = separating i b k)
    (hnonseparating : ∀ b, nonseparatingPart cache j b = nonseparating b) :
    originalWeighted j = fundamental +
      (∑ i : Fin 4, ∑ b : SurfaceBasisLabel X, ∑ k : Fin 2, separating i b k) +
      ∑ b : SurfaceBasisLabel X, nonseparating b := by
  rw [originalWeighted_eq_rootSum cache j h, rootSum, hfundamental]
  simp only [hseparating, hnonseparating]

/-- Reuse the complete original term-121 certificate, regardless of the chosen new cache. -/
theorem originalWeighted121 : originalWeighted 121 = 1 / 2160 :=
  BlowupF1H121OuterParts.original_weighted121

/-- The new root sum reuses the old certificate for every certified cache. -/
theorem rootSum121 (cache : ResidualCache X) : rootSum cache 121 = 1 / 2160 :=
  (originalWeighted_eq_rootSum cache 121 (by decide +kernel)).symm.trans originalWeighted121

/-- Restore all 815 original indices, including the coefficient-zero entries. -/
theorem pointConstantGuarded_eq_sum_originalWeighted :
    L24Relation.pointConstantGuarded X 1 sourceCurve insertions =
      ∑ j : Fin 815, originalWeighted j :=
  L24Relation.pointConstantGuarded_eq_fullFrame X 1 sourceCurve insertions

/-- Assemble a complete checked value table on the original frame. -/
theorem pointConstantGuarded_eq_sum_claims (claimed : Fin 815 → ℚ)
    (hclaimed : ∀ j, originalWeighted j = claimed j) :
    L24Relation.pointConstantGuarded X 1 sourceCurve insertions =
      ∑ j : Fin 815, claimed j := by
  rw [pointConstantGuarded_eq_sum_originalWeighted]
  exact Finset.sum_congr rfl (fun j _ ↦ hclaimed j)

end AxiomaticGW.BlowupF1RootAssembly
