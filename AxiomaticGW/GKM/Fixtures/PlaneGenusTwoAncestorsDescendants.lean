/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsData

/-!
# Plane descendant arithmetic using the candidate ancestor table

Input SHA256: 640e00ec2d4b2055c49465d80a3590da42dec51772d34ea00bad356dad0950a8
Candidate values become certificates only after their full equations are checked.
The original canonical seeds and geometric hypotheses are unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoAncestors

open BelorousskiPandharipande SurfaceGenusTwo

-- This calculation is conditional on the separately checked ancestor table.
/-- The original genus-two comparison, preserving each ordered insertion. -/
def mixedTerms (q : SurfaceQuery .plane) : RationalTerms (SurfaceAncestorKey .plane) :=
  SurfaceDescendant.mixedAncestorTerms 2 (Fin q.insertions.length)
    (by simp only [StableArity, Fintype.card_fin]; omega)
    (List.finRange q.insertions.length) q.beta
    (fun i ↦ (q.insertions.get i).psi) 0 (fun i ↦ (q.insertions.get i).label)

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 0. -/
@[nolint defsWithUnderscore]
def comparisonTerms_0 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 6}),
    (1, {key 28}),
    (3, {key 2}),
    (6, {key 0})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_0 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 0) =
      comparisonTerms_0 := by decide +kernel

private theorem cached_0 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 0) =
      some (PlaneGenusTwoFewMarkingsReplay.values 0) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 0))) = _
  rw [comparison_0]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 1. -/
@[nolint defsWithUnderscore]
def comparisonTerms_1 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 6}),
    (-2, {key 2}),
    (-3, {key 0}),
    (1, {key 19})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_1 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 1) =
      comparisonTerms_1 := by decide +kernel

private theorem cached_1 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 1) =
      some (PlaneGenusTwoFewMarkingsReplay.values 1) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 1))) = _
  rw [comparison_1]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 2. -/
@[nolint defsWithUnderscore]
def comparisonTerms_2 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 6}),
    (1, {key 2}),
    (1, {key 0}),
    (1, {key 12})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_2 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 2) =
      comparisonTerms_2 := by decide +kernel

private theorem cached_2 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 2) =
      some (PlaneGenusTwoFewMarkingsReplay.values 2) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 2))) = _
  rw [comparison_2]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 3. -/
@[nolint defsWithUnderscore]
def comparisonTerms_3 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 13}),
    (1, {key 35}),
    (3, {key 7}),
    (6, {key 3})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_3 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 3) =
      comparisonTerms_3 := by decide +kernel

private theorem cached_3 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 3) =
      some (PlaneGenusTwoFewMarkingsReplay.values 3) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 3))) = _
  rw [comparison_3]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 4. -/
@[nolint defsWithUnderscore]
def comparisonTerms_4 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 14}),
    (1, {key 36}),
    (3, {key 8}),
    (6, {key 4})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_4 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 4) =
      comparisonTerms_4 := by decide +kernel

private theorem cached_4 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 4) =
      some (PlaneGenusTwoFewMarkingsReplay.values 4) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 4))) = _
  rw [comparison_4]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 5. -/
@[nolint defsWithUnderscore]
def comparisonTerms_5 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 14}),
    (1, {key 37}),
    (3, {key 9})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_5 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 5) =
      comparisonTerms_5 := by decide +kernel

private theorem cached_5 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 5) =
      some (PlaneGenusTwoFewMarkingsReplay.values 5) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 5))) = _
  rw [comparison_5]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 6. -/
@[nolint defsWithUnderscore]
def comparisonTerms_6 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 13}),
    (1, {key 13}),
    (1, {key 38})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_6 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 6) =
      comparisonTerms_6 := by decide +kernel

private theorem cached_6 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 6) =
      some (PlaneGenusTwoFewMarkingsReplay.values 6) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 6))) = _
  rw [comparison_6]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 7. -/
@[nolint defsWithUnderscore]
def comparisonTerms_7 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 14}),
    (1, {key 37}),
    (3, {key 9})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_7 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 7) =
      comparisonTerms_7 := by decide +kernel

private theorem cached_7 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 7) =
      some (PlaneGenusTwoFewMarkingsReplay.values 7) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 7))) = _
  rw [comparison_7]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 8. -/
@[nolint defsWithUnderscore]
def comparisonTerms_8 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 14}),
    (1, {key 36}),
    (3, {key 8}),
    (6, {key 4})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_8 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 8) =
      comparisonTerms_8 := by decide +kernel

private theorem cached_8 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 8) =
      some (PlaneGenusTwoFewMarkingsReplay.values 8) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 8))) = _
  rw [comparison_8]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 9. -/
@[nolint defsWithUnderscore]
def comparisonTerms_9 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 13}),
    (1, {key 35}),
    (3, {key 7}),
    (6, {key 3})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_9 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 9) =
      comparisonTerms_9 := by decide +kernel

private theorem cached_9 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 9) =
      some (PlaneGenusTwoFewMarkingsReplay.values 9) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 9))) = _
  rw [comparison_9]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 10. -/
@[nolint defsWithUnderscore]
def comparisonTerms_10 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 13}),
    (-2, {key 7}),
    (-3, {key 3}),
    (1, {key 29})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_10 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 10) =
      comparisonTerms_10 := by decide +kernel

private theorem cached_10 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 10) =
      some (PlaneGenusTwoFewMarkingsReplay.values 10) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 10))) = _
  rw [comparison_10]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 11. -/
@[nolint defsWithUnderscore]
def comparisonTerms_11 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 14}),
    (-2, {key 8}),
    (-3, {key 4}),
    (1, {key 30})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_11 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 11) =
      comparisonTerms_11 := by decide +kernel

private theorem cached_11 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 11) =
      some (PlaneGenusTwoFewMarkingsReplay.values 11) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 11))) = _
  rw [comparison_11]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 12. -/
@[nolint defsWithUnderscore]
def comparisonTerms_12 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 14}),
    (-2, {key 9}),
    (1, {key 31})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_12 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 12) =
      comparisonTerms_12 := by decide +kernel

private theorem cached_12 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 12) =
      some (PlaneGenusTwoFewMarkingsReplay.values 12) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 12))) = _
  rw [comparison_12]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 13. -/
@[nolint defsWithUnderscore]
def comparisonTerms_13 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 13}),
    (1, {key 7}),
    (1, {key 32})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_13 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 13) =
      comparisonTerms_13 := by decide +kernel

private theorem cached_13 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 13) =
      some (PlaneGenusTwoFewMarkingsReplay.values 13) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 13))) = _
  rw [comparison_13]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 14. -/
@[nolint defsWithUnderscore]
def comparisonTerms_14 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 8}),
    (1, {key 33}),
    (3, {key 5})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_14 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 14) =
      comparisonTerms_14 := by decide +kernel

private theorem cached_14 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 14) =
      some (PlaneGenusTwoFewMarkingsReplay.values 14) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 14))) = _
  rw [comparison_14]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 15. -/
@[nolint defsWithUnderscore]
def comparisonTerms_15 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 9}),
    (1, {key 34}),
    (3, {key 5}),
    (6, {key 1})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_15 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 15) =
      comparisonTerms_15 := by decide +kernel

private theorem cached_15 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 15) =
      some (PlaneGenusTwoFewMarkingsReplay.values 15) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 15))) = _
  rw [comparison_15]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 16. -/
@[nolint defsWithUnderscore]
def comparisonTerms_16 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 13}),
    (1, {key 7}),
    (1, {key 3}),
    (1, {key 20})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_16 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 16) =
      comparisonTerms_16 := by decide +kernel

private theorem cached_16 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 16) =
      some (PlaneGenusTwoFewMarkingsReplay.values 16) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 16))) = _
  rw [comparison_16]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 17. -/
@[nolint defsWithUnderscore]
def comparisonTerms_17 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 14}),
    (1, {key 8}),
    (1, {key 4}),
    (1, {key 21})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_17 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 17) =
      comparisonTerms_17 := by decide +kernel

private theorem cached_17 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 17) =
      some (PlaneGenusTwoFewMarkingsReplay.values 17) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 17))) = _
  rw [comparison_17]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 18. -/
@[nolint defsWithUnderscore]
def comparisonTerms_18 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 14}),
    (1, {key 9}),
    (1, {key 22})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_18 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 18) =
      comparisonTerms_18 := by decide +kernel

private theorem cached_18 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 18) =
      some (PlaneGenusTwoFewMarkingsReplay.values 18) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 18))) = _
  rw [comparison_18]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 19. -/
@[nolint defsWithUnderscore]
def comparisonTerms_19 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 13}),
    (1, {key 3}),
    (1, {key 23})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_19 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 19) =
      comparisonTerms_19 := by decide +kernel

private theorem cached_19 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 19) =
      some (PlaneGenusTwoFewMarkingsReplay.values 19) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 19))) = _
  rw [comparison_19]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 20. -/
@[nolint defsWithUnderscore]
def comparisonTerms_20 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 4}),
    (1, {key 24}),
    (3, {key 1})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_20 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 20) =
      comparisonTerms_20 := by decide +kernel

private theorem cached_20 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 20) =
      some (PlaneGenusTwoFewMarkingsReplay.values 20) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 20))) = _
  rw [comparison_20]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 21. -/
@[nolint defsWithUnderscore]
def comparisonTerms_21 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 9}),
    (1, {key 34}),
    (3, {key 5}),
    (6, {key 1})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_21 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 21) =
      comparisonTerms_21 := by decide +kernel

private theorem cached_21 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 21) =
      some (PlaneGenusTwoFewMarkingsReplay.values 21) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 21))) = _
  rw [comparison_21]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 22. -/
@[nolint defsWithUnderscore]
def comparisonTerms_22 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 8}),
    (1, {key 33}),
    (3, {key 5})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_22 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 22) =
      comparisonTerms_22 := by decide +kernel

private theorem cached_22 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 22) =
      some (PlaneGenusTwoFewMarkingsReplay.values 22) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 22))) = _
  rw [comparison_22]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 23. -/
@[nolint defsWithUnderscore]
def comparisonTerms_23 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 13}),
    (1, {key 7}),
    (1, {key 32})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_23 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 23) =
      comparisonTerms_23 := by decide +kernel

private theorem cached_23 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 23) =
      some (PlaneGenusTwoFewMarkingsReplay.values 23) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 23))) = _
  rw [comparison_23]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 24. -/
@[nolint defsWithUnderscore]
def comparisonTerms_24 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 14}),
    (-2, {key 9}),
    (1, {key 31})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_24 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 24) =
      comparisonTerms_24 := by decide +kernel

private theorem cached_24 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 24) =
      some (PlaneGenusTwoFewMarkingsReplay.values 24) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 24))) = _
  rw [comparison_24]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 25. -/
@[nolint defsWithUnderscore]
def comparisonTerms_25 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 14}),
    (-2, {key 8}),
    (-3, {key 4}),
    (1, {key 30})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_25 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 25) =
      comparisonTerms_25 := by decide +kernel

private theorem cached_25 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 25) =
      some (PlaneGenusTwoFewMarkingsReplay.values 25) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 25))) = _
  rw [comparison_25]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 26. -/
@[nolint defsWithUnderscore]
def comparisonTerms_26 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 13}),
    (-2, {key 7}),
    (-3, {key 3}),
    (1, {key 29})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_26 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 26) =
      comparisonTerms_26 := by decide +kernel

private theorem cached_26 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 26) =
      some (PlaneGenusTwoFewMarkingsReplay.values 26) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 26))) = _
  rw [comparison_26]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 27. -/
@[nolint defsWithUnderscore]
def comparisonTerms_27 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 9}),
    (-2, {key 5}),
    (-3, {key 1}),
    (1, {key 25})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_27 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 27) =
      comparisonTerms_27 := by decide +kernel

private theorem cached_27 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 27) =
      some (PlaneGenusTwoFewMarkingsReplay.values 27) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 27))) = _
  rw [comparison_27]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 28. -/
@[nolint defsWithUnderscore]
def comparisonTerms_28 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 8}),
    (-2, {key 5}),
    (1, {key 26})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_28 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 28) =
      comparisonTerms_28 := by decide +kernel

private theorem cached_28 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 28) =
      some (PlaneGenusTwoFewMarkingsReplay.values 28) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 28))) = _
  rw [comparison_28]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 29. -/
@[nolint defsWithUnderscore]
def comparisonTerms_29 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 7}),
    (-1, {key 7}),
    (1, {key 27})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_29 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 29) =
      comparisonTerms_29 := by decide +kernel

private theorem cached_29 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 29) =
      some (PlaneGenusTwoFewMarkingsReplay.values 29) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 29))) = _
  rw [comparison_29]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 30. -/
@[nolint defsWithUnderscore]
def comparisonTerms_30 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 8}),
    (-2, {key 5}),
    (1, {key 26})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_30 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 30) =
      comparisonTerms_30 := by decide +kernel

private theorem cached_30 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 30) =
      some (PlaneGenusTwoFewMarkingsReplay.values 30) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 30))) = _
  rw [comparison_30]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 31. -/
@[nolint defsWithUnderscore]
def comparisonTerms_31 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 9}),
    (-2, {key 5}),
    (-3, {key 1}),
    (1, {key 25})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_31 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 31) =
      comparisonTerms_31 := by decide +kernel

private theorem cached_31 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 31) =
      some (PlaneGenusTwoFewMarkingsReplay.values 31) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 31))) = _
  rw [comparison_31]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 32. -/
@[nolint defsWithUnderscore]
def comparisonTerms_32 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 9}),
    (1, {key 5}),
    (1, {key 1}),
    (1, {key 15})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_32 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 32) =
      comparisonTerms_32 := by decide +kernel

private theorem cached_32 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 32) =
      some (PlaneGenusTwoFewMarkingsReplay.values 32) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 32))) = _
  rw [comparison_32]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 33. -/
@[nolint defsWithUnderscore]
def comparisonTerms_33 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 8}),
    (1, {key 5}),
    (1, {key 16})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_33 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 33) =
      comparisonTerms_33 := by decide +kernel

private theorem cached_33 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 33) =
      some (PlaneGenusTwoFewMarkingsReplay.values 33) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 33))) = _
  rw [comparison_33]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 34. -/
@[nolint defsWithUnderscore]
def comparisonTerms_34 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 3}),
    (1, {key 7}),
    (1, {key 17})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_34 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 34) =
      comparisonTerms_34 := by decide +kernel

private theorem cached_34 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 34) =
      some (PlaneGenusTwoFewMarkingsReplay.values 34) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 34))) = _
  rw [comparison_34]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 35. -/
@[nolint defsWithUnderscore]
def comparisonTerms_35 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 4}),
    (-2, {key 1}),
    (1, {key 18})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_35 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 35) =
      comparisonTerms_35 := by decide +kernel

private theorem cached_35 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 35) =
      some (PlaneGenusTwoFewMarkingsReplay.values 35) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 35))) = _
  rw [comparison_35]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 36. -/
@[nolint defsWithUnderscore]
def comparisonTerms_36 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 4}),
    (1, {key 24}),
    (3, {key 1})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_36 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 36) =
      comparisonTerms_36 := by decide +kernel

private theorem cached_36 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 36) =
      some (PlaneGenusTwoFewMarkingsReplay.values 36) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 36))) = _
  rw [comparison_36]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 37. -/
@[nolint defsWithUnderscore]
def comparisonTerms_37 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 13}),
    (1, {key 3}),
    (1, {key 23})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_37 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 37) =
      comparisonTerms_37 := by decide +kernel

private theorem cached_37 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 37) =
      some (PlaneGenusTwoFewMarkingsReplay.values 37) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 37))) = _
  rw [comparison_37]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 38. -/
@[nolint defsWithUnderscore]
def comparisonTerms_38 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 14}),
    (1, {key 9}),
    (1, {key 22})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_38 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 38) =
      comparisonTerms_38 := by decide +kernel

private theorem cached_38 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 38) =
      some (PlaneGenusTwoFewMarkingsReplay.values 38) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 38))) = _
  rw [comparison_38]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 39. -/
@[nolint defsWithUnderscore]
def comparisonTerms_39 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 14}),
    (1, {key 8}),
    (1, {key 4}),
    (1, {key 21})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_39 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 39) =
      comparisonTerms_39 := by decide +kernel

private theorem cached_39 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 39) =
      some (PlaneGenusTwoFewMarkingsReplay.values 39) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 39))) = _
  rw [comparison_39]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 40. -/
@[nolint defsWithUnderscore]
def comparisonTerms_40 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 13}),
    (1, {key 7}),
    (1, {key 3}),
    (1, {key 20})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_40 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 40) =
      comparisonTerms_40 := by decide +kernel

private theorem cached_40 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 40) =
      some (PlaneGenusTwoFewMarkingsReplay.values 40) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 40))) = _
  rw [comparison_40]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 41. -/
@[nolint defsWithUnderscore]
def comparisonTerms_41 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 4}),
    (-2, {key 1}),
    (1, {key 18})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_41 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 41) =
      comparisonTerms_41 := by decide +kernel

private theorem cached_41 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 41) =
      some (PlaneGenusTwoFewMarkingsReplay.values 41) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 41))) = _
  rw [comparison_41]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 42. -/
@[nolint defsWithUnderscore]
def comparisonTerms_42 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (-1, {key 3}),
    (1, {key 7}),
    (1, {key 17})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_42 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 42) =
      comparisonTerms_42 := by decide +kernel

private theorem cached_42 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 42) =
      some (PlaneGenusTwoFewMarkingsReplay.values 42) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 42))) = _
  rw [comparison_42]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 43. -/
@[nolint defsWithUnderscore]
def comparisonTerms_43 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 8}),
    (1, {key 5}),
    (1, {key 16})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_43 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 43) =
      comparisonTerms_43 := by decide +kernel

private theorem cached_43 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 43) =
      some (PlaneGenusTwoFewMarkingsReplay.values 43) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 43))) = _
  rw [comparison_43]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 44. -/
@[nolint defsWithUnderscore]
def comparisonTerms_44 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 9}),
    (1, {key 5}),
    (1, {key 1}),
    (1, {key 15})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_44 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 44) =
      comparisonTerms_44 := by decide +kernel

private theorem cached_44 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 44) =
      some (PlaneGenusTwoFewMarkingsReplay.values 44) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 44))) = _
  rw [comparison_44]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 45. -/
@[nolint defsWithUnderscore]
def comparisonTerms_45 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 4}),
    (1, {key 1}),
    (1, {key 10})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_45 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 45) =
      comparisonTerms_45 := by decide +kernel

private theorem cached_45 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 45) =
      some (PlaneGenusTwoFewMarkingsReplay.values 45) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 45))) = _
  rw [comparison_45]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 46. -/
@[nolint defsWithUnderscore]
def comparisonTerms_46 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 3}),
    (1, {key 3}),
    (1, {key 11})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_46 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 46) =
      comparisonTerms_46 := by decide +kernel

private theorem cached_46 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 46) =
      some (PlaneGenusTwoFewMarkingsReplay.values 46) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 46))) = _
  rw [comparison_46]
  decide +kernel

-- Preserve the stable numeric row names used by the certificate exchange.
/-- Candidate comparison terms for the complete held request 47. -/
@[nolint defsWithUnderscore]
def comparisonTerms_47 : RationalTerms (SurfaceAncestorKey .plane) :=
  {
    (1, {key 4}),
    (1, {key 1}),
    (1, {key 10})}

/-- Check the expansion before evaluating any candidate ancestor values. -/
theorem comparison_47 :
    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 47) =
      comparisonTerms_47 := by decide +kernel

private theorem cached_47 :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests 47) =
      some (PlaneGenusTwoFewMarkingsReplay.values 47) := by
  change some (RationalTerms.eval (ancestorValueCached
    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)
    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests 47))) = _
  rw [comparison_47]
  decide +kernel

/-- Every full incoming request is evaluated using the declared candidate cache. -/
theorem cached_computation (i : Fin 48) :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (PlaneGenusTwoFewMarkingsReplay.requests i) =
      some (PlaneGenusTwoFewMarkingsReplay.values i) := by
  fin_cases i
  · exact cached_0
  · exact cached_1
  · exact cached_2
  · exact cached_3
  · exact cached_4
  · exact cached_5
  · exact cached_6
  · exact cached_7
  · exact cached_8
  · exact cached_9
  · exact cached_10
  · exact cached_11
  · exact cached_12
  · exact cached_13
  · exact cached_14
  · exact cached_15
  · exact cached_16
  · exact cached_17
  · exact cached_18
  · exact cached_19
  · exact cached_20
  · exact cached_21
  · exact cached_22
  · exact cached_23
  · exact cached_24
  · exact cached_25
  · exact cached_26
  · exact cached_27
  · exact cached_28
  · exact cached_29
  · exact cached_30
  · exact cached_31
  · exact cached_32
  · exact cached_33
  · exact cached_34
  · exact cached_35
  · exact cached_36
  · exact cached_37
  · exact cached_38
  · exact cached_39
  · exact cached_40
  · exact cached_41
  · exact cached_42
  · exact cached_43
  · exact cached_44
  · exact cached_45
  · exact cached_46
  · exact cached_47

end AxiomaticGW.GKM.PlaneGenusTwoAncestors
