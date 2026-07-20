# Project notes

The documentation is divided according to its purpose.

## Mathematics and Lean

The [mathematics-to-Lean map](MathematicsToLean.md) connects mathematical-note sections to implementing source modules and principal declarations. It also records mathematical topics that are deliberately not yet formalized.

## Mathematics

The [`mathematics`](mathematics/) folder contains self-contained mathematical exposition. These notes explain definitions, constructions, identities, and the mathematical relationships between the stages of axiomatic Gromov--Witten theory. They may report the current formalization boundary, but they are not used to schedule implementation work.

- [Mathematics notes for M1--M10](mathematics/README.md)
- [The mathematics and goals of AxiomaticGW](mathematics/ProjectMathematicsAndGoals.md)
- [Core structure dependencies](mathematics/CoreStructureDependencies.md)
- [The point target and stable-curve intersection theory](mathematics/PointTargetAndStableCurves.md)

## Formalization reviews

The [`reviews`](reviews/) folder contains targeted audits of existing Lean modules and test infrastructure. These records distinguish mathematical findings, API checks, validation evidence, and remaining uncertainty; accepted project-wide status remains in the milestone records.

- [Review index](reviews/README.md)
- [Linear and Frobenius review guide](reviews/LinearFrobeniusReviewGuide.md)
- [Symmetric perfect-pairing review](reviews/Linear/PerfectPairing.md)
- [Basic regression-test suite review](reviews/TestSuite/Basic.md)

## Milestones

The [`milestones`](milestones/) folder contains implementation roadmaps, completion criteria, dependency order, and the status of the Lean development. Milestone documents should link to the corresponding mathematical notes rather than repeat their full exposition.

- [Topological field theory milestones](milestones/TopologicalTFTMilestones.md)
- [Roadmap to axiomatic Gromov--Witten theory](milestones/AxiomaticGWRoadmap.md)
- [Implementation progress and verification record](milestones/ImplementationProgress.md)
- [Mathematical terminology audit](milestones/TerminologyAudit.md)
