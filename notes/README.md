# Project notes

The documentation is divided according to its purpose.

## Mathematics and Lean

The [mathematics-to-Lean map](MathematicsToLean.md) connects mathematical-note sections to implementing source modules and principal declarations. It also records mathematical topics that are deliberately not yet formalized.

## Mathematics

The [`mathematics`](mathematics/) folder contains self-contained mathematical exposition. These notes explain definitions, constructions, identities, and the mathematical relationships between the stages of axiomatic Gromov--Witten theory. They may report the current formalization boundary, but they are not used to schedule implementation work.

- [Mathematics notes for M1--M10](mathematics/README.md)
- [The mathematics and goals of AxiomaticGW](mathematics/ProjectMathematicsAndGoals.md)

## Milestones

The [`milestones`](milestones/) folder contains implementation roadmaps, completion criteria, dependency order, and the status of the Lean development. Milestone documents should link to the corresponding mathematical notes rather than repeat their full exposition.

- [Topological field theory milestones](milestones/TopologicalTFTMilestones.md)
- [Roadmap to axiomatic Gromov--Witten theory](milestones/AxiomaticGWRoadmap.md)
- [Implementation progress and verification record](milestones/ImplementationProgress.md)
