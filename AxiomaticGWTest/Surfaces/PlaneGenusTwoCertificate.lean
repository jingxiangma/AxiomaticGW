import AxiomaticGW.Surfaces.PlaneGenusTwoCertificate

open AxiomaticGW BelorousskiPandharipande

-- The original initial equation has a checked constant, not an extra numerical input.
example : planeShiftedConstant 0 1 = 1 / 80 := planeShiftedConstant_initial

example : planeCanonicalValues 0 = ![0, -1 / 960, 0] := planeCanonicalValues_initial

-- The shifted quartic equations consume certified degree-five lower-genus support.
example : SurfaceGenusTwo.planeRationalPointValue ![5] = 87304 := by decide +kernel

example : SurfaceGenusTwo.planeEllipticPointValue ![5] = 87192 := by decide +kernel

-- Internal queries beyond the cached energy bound retain the original algorithms.
example : SurfaceGenusTwo.planeRationalPointValue ![6] =
    SurfaceGenusZero.pointValue .plane ![6] :=
  congrFun SurfaceGenusTwo.planeRationalPointValue_eq ![6]

example : SurfaceGenusTwo.planeEllipticPointValue ![6] =
    SurfaceGenusOne.pointValue .plane ![6] :=
  congrFun SurfaceGenusTwo.planeEllipticPointValue_eq ![6]

-- The BP constant has total genus two, but each of its components is low genus.
example : (paperTerm 4).1.maxComponentGenus = 1 := by decide +kernel

example : SurfaceGenusOne.requiredPoints .plane (paperTerm 4).1 ![2]
    ![.hyperplane, .hyperplane, .point] = 4 := by decide +kernel

-- Pruning rejects the wrong marking count for arbitrary candidate primary values.
example (v₀ v₁ : SurfaceTarget.plane.Curve → ℚ) :
    SurfaceGenusOne.primaryGraphDimensionEval .plane v₀ v₁ (paperTerm 4).1 ![2] 3
      ![.hyperplane, .hyperplane, .point] = 0 := by
  rw [SurfaceGenusOne.primaryGraphDimensionEval_eq]
  apply SurfaceGenusOne.primaryGraphEval_eq_zero_of_points_ne
  decide +kernel

-- Its interpretation uses the component-genus bound, not an impossible total-genus bound.
example (v₀ v₁ : SurfaceTarget.plane.Curve → ℚ) (n : ℕ)
    (beta : SurfaceTarget.plane.Curve) (a : Fin 3 → SurfaceBasisLabel .plane) :
    SurfaceGenusOne.primaryGraphDimensionEval .plane v₀ v₁ (paperTerm 4).1 beta n a =
      (paperTerm 4).1.pointContraction .plane
        (SurfaceGenusTwo.primaryConstantPointVertex .plane v₀ v₁)
        (paperTerm 4).1.zeroDecoration (paperLabelDecisions 4) beta n a := by
  rw [SurfaceGenusOne.primaryGraphDimensionEval_eq]
  exact SurfaceGenusTwo.primaryGraphEval_pointContraction_eq .plane v₀ v₁
    (paperTerm 4).1 (by decide) (paperLabelDecisions 4) beta n a

-- A loop does not hide the genus-two component, even in a graph of total genus three.
private def loopTerm : GluingExpression.CotangentTerm 3 (Fin 1) :=
  ⟨(GluingExpression.fundamental 2 (Option (Option (Fin 1)))
      (by change 3 ≤ 7; decide)).nonseparating,
    0, (inferInstance : DecidableEq (Option (Option (Fin 1))))⟩

example (X : SurfaceTarget) (beta : X.Curve) (n : ℕ)
    (a : Fin 1 → SurfaceBasisLabel X) :
    loopTerm.expression.pointContraction X
      (SurfacePointPullback.vertex X (SurfaceGenusTwo.constantVertex X))
      loopTerm.decoration loopTerm.labels beta n a = 0 :=
  SurfaceGenusTwo.point_constant_eq_zero X loopTerm (by decide) beta n a

private def initialTable : ℕ → Fin 3 → ℚ := fun _ ↦ ![0, -1 / 960, 0]

example : planeCheckCanonicalTable 0 initialTable = true := by decide +kernel

example : planeCheckCanonicalClaim 0 initialTable (planeCanonicalQueries 0 1) (-1 / 960) =
    true := by decide +kernel

-- An altered value cannot reuse the accepted initial table.
example : planeCheckCanonicalClaim 0 initialTable (planeCanonicalQueries 0 1) 0 = false := by
  decide +kernel

-- The same numerical zero is insufficient when the requested degree is outside the bound.
example : planeCheckCanonicalClaim 0 initialTable (planeCanonicalQueries 1 0) 0 = false := by
  decide +kernel

-- Query genus and insertion data remain part of the independently held request.
example : planeCheckCanonicalClaim 0 initialTable
    (SurfaceQuery.points .plane 1 ![0] 1) 0 = false := by decide +kernel

-- The derived initial triple cannot be replaced by a candidate zero oracle.
example : planeCheckCanonicalTable 0 (fun _ _ ↦ 0) = false := by decide +kernel

-- The positive-degree step ignores every candidate entry at or above the current degree.
example (v w : ℕ → Fin 3 → ℚ) (h : v 0 = w 0) (i : Fin 3) :
    planeScalarRemainder v 1 i = planeScalarRemainder w 1 i := by
  apply planeScalarRemainder_congr
  intro b hb
  have hz : b = 0 := by omega
  simpa only [hz] using h
