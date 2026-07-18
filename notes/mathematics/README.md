# Mathematics notes

This folder contains the mathematical background for the formalization. A note here should explain the mathematics independently of the order in which the Lean code is implemented.

For a single self-contained introduction, see [The mathematics and goals of AxiomaticGW](ProjectMathematicsAndGoals.md).

The numbering agrees with the phases in the [project-wide milestone roadmap](../milestones/AxiomaticGWRoadmap.md).

| Phase | Mathematical note |
| --- | --- |
| M1 | [Perfect pairings and Frobenius algebras](M01PerfectPairingsAndFrobeniusAlgebras.md) |
| M2 | [Two-dimensional topological field theory](M02TwoDimensionalTFT.md) |
| M3 | [Stable curves and gluing](M03StableCurvesAndGluing.md) |
| M4 | [Full unital CohFT](M04FullUnitalCohFT.md) |
| M5 | [Tautological classes and ancestors](M05TautologicalClassesAndAncestors.md) |
| M6 | [Curve-class-resolved GW axioms](M06CurveClassResolvedGW.md) |
| M7 | [Novikov coefficients and quantum products](M07NovikovAndQuantumProducts.md) |
| M8 | [Descendants and descendant--ancestor comparison](M08DescendantsAndAncestors.md) |
| M9 | [All-genus potentials and equations](M09PotentialsAndEquations.md) |
| M10 | [Geometric realization](M10GeometricRealization.md) |

The focused note [The point target and stable-curve intersection theory](PointTargetAndStableCurves.md) gives the first universal regression case beyond the constant degree-zero model and records the all-genus DVV formula.

The formulas and terminology in these notes are checked against searchable arXiv TeX sources: Kontsevich--Manin for GW classes, CohFT gluing, grading, unit, divisor, and WDVV; Givental for descendant and ancestor potentials, calibrations, symplecticity, and Fock-space qualifications; Mulase--Safnuk for psi-class intersections, dimension constraints, and Virasoro/DVV normalization; Dumitrescu for the two-dimensional TFT/Frobenius correspondence; Getzler for the codimension-two relation and excess-intersection normalization on $\overline{\mathcal M}_{1,4}$; and Delecroix--Schmitt--van Zelm for decorated-stratum and `admcycles` conventions. Source metadata and the audited topics are recorded in the [online reference ledger](../references/online/README.md).

The canonical mapping from mathematical sections to Lean modules is maintained in the [mathematics-to-Lean map](../MathematicsToLean.md). Dated implementation status and verification evidence belong in the [`implementation progress record`](../milestones/ImplementationProgress.md), not in these mathematical notes.
