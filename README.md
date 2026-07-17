# AxiomaticGW

Lean formalization of the algebraic foundations of axiomatic Gromov--Witten theory.

The repository is the home of the full project, developed in verified layers. The Frobenius/TFT and full CohFT foundations are implemented, as are the axiomatic GW interfaces for tautological ancestors, positive effective curve classes, beta-resolved primary classes, Novikov coefficients, quantum-product laws, stable-map descendants, descendant--ancestor comparison, formal potentials, Laurent total free energies, and the abstract virtual-realization boundary.

> **Project status:** active, research-stage development. The axiomatic interfaces compile without `sorry` or `admit`. Coefficientwise small WDVV and associativity, invariant-defined potentials, the formal big product with its small specialization, and the point-target stable-curve block are implemented. Concrete geometric stable-map and stable-curve instances remain future realization work.

> **Scope:** Stable-curve targets are abstract even graded cohomology algebras and are not assumed finite free. Novikov completion is therefore coefficientwise for cohomology-valued classes; numerical coefficients and the finite-free state space carry the completed convolution operations.

## Project progress

The [mathematics-to-Lean map](notes/MathematicsToLean.md) connects the mathematical notes to source modules and principal declarations. The [implementation progress record](notes/milestones/ImplementationProgress.md) provides dated milestone scope, verification evidence, implementation commits, deferred work, and the next development gate. The [roadmap](notes/milestones/AxiomaticGWRoadmap.md) remains the source of truth for current milestone status and ordering.

## Getting started

Install Lean with [elan](https://github.com/leanprover/elan), clone the repository, and run:

```bash
lake exe cache get
lake build
lake test
```

The project pins Lean and mathlib to `v4.32.0`. Import the current public API with:

```lean
import AxiomaticGW
```

Run `lake lint` before submitting changes. CI performs the build, test, and lint steps on every pull request to `main`.

## Final scope

The endpoint is an **all-genus axiomatic Gromov--Witten theory**, resolved by curve class and equipped with the complete descendant package. In particular, the final theory is intended to support

- primary GW classes for every stable `(g, S)` and every effective curve class;
- separating and nonseparating gluing, the flat unit, grading, virtual dimension, effectivity, and the divisor axiom;
- descendant insertions indexed by arbitrary powers of stable-map `psi`-classes;
- ancestor insertions using stable-curve `psi`-classes, together with the descendant--ancestor comparison;
- a beta-preserving Novikov completion over a positive locally finite effective curve-class monoid;
- all-genus descendant and ancestor genus potentials and total free energies;
- string, dilaton, divisor, splitting, genus-reduction, and tautological relations whenever the required abstract geometric operations are present.

A bare CohFT already contains all stable genera. The genus-zero API is only a derived restriction used to prove associativity and WDVV. Descendants are not fields of the minimal CohFT structure: they require `psi`-classes, pushforwards, integration, and projection formulas. Moreover, stable-map descendants and stable-curve ancestors are kept distinct.

## Architecture

The intended dependency direction is

```text
Mathlib -> Linear -> Frobenius -> TFT
              \                    \
               -> Combinatorics -> CohFT -> GW -> Geometry
               -> Coefficients ------------/
```

The implemented source layout is:

```text
AxiomaticGW/
  Linear/
    PerfectPairing.lean
    Copairing.lean
    Contraction.lean

  Frobenius/
    Basic.lean
    Constructions.lean
    Coalgebra.lean
    Examples.lean

  TFT/
    FiniteProduct.lean
    Correlator.lean
    Sewing.lean
    Basic.lean
    Frobenius.lean
    Classification.lean
    Examples.lean

  Combinatorics/
    StableArity.lean

  Coefficients/
    EffectiveCurveClass.lean
    Novikov.lean
    GenusExpansion.lean
    DescendantVariables.lean

  CohFT/
    Topological.lean           # implemented scalar-valued stable theory
    StableCurve.lean           # implemented abstract even-cohomology targets
    Basic.lean                 # implemented full all-genus CohFT
    Constant.lean              # implemented degree-zero model and conversion
    GenusZero.lean             # implemented genus-zero restriction
    Frobenius.lean             # implemented extraction, WDVV, associativity
    TopologicalPart.lean       # implemented degree-zero scalarization
    Classification.lean       # implemented stable-arity Frobenius round trip
    Tautological.lean          # psi, integration, pushforward, kappa
    Ancestors.lean             # stable-curve ancestor correlators

  GW/
    Basic.lean                 # beta-resolved, full all-genus primary theory
    QuantumProduct.lean        # derived small WDVV and associativity
    Constant.lean              # beta-zero reference model
    FormalQuantumProduct.lean  # formal big product and small specialization
    Descendants/
      Basic.lean               # stable-map descendant classes
      Comparison.lean          # descendants versus ancestors
      Equations.lean           # string, dilaton, divisor law package
      Potentials.lean          # invariant-defined descendant/ancestor series

  Point/
    Descendants.lean           # stable-curve intersections and DVV relation

  Geometry/
    VirtualGWPackage.lean
```

Only modules with implemented content are created. Future concrete targets and geometric realizations will be added when they carry proofs rather than placeholder declarations.

The essential formalization chain is

```text
perfect duality and contractions
  -> Frobenius algebra and topological CohFT
  -> full all-genus CohFT
  -> beta-resolved all-genus primary GW theory
  -> Novikov coefficients and quantum-product WDVV
  -> descendants, ancestors, comparison, and total free energies
  -> abstract output boundary for virtual stable-map geometry
```

## Completed foundations

The completed Frobenius API now follows the chain

```text
counit -> trace pairing -> perfect duality -> symmetric copairing
       -> comultiplication -> cocommutative coalgebra -> Frobenius relation
       -> handle element.
```

The core definitions and proofs are basis-free. `CommFrobeniusAlgebra` is an explicit object rather than a typeclass, since a fixed algebra can admit more than one Frobenius functional. Its canonical coalgebra can be installed as a local mathlib instance when needed.

The completed topological-theory layer follows the chain

```text
finite-labelled multiplication
  -> all-genus Frobenius correlators
  -> basis-free named-slot contraction
  -> separating and nonseparating sewing
  -> bundled topological correlator theory
  -> stable scalar-valued topological CohFT
  -> recovery of the counit and three-point product
  -> full stable-arity Frobenius classification.
```

The geometric oriented bordism category is not formalized: `TopologicalCorrelatorTheory` is its algebraic correlator presentation. `TopologicalCohFT` remains the scalar-valued degree-zero theory, while `CohFT` is valued in an abstract `StableCurveCohomology`. The constant target connects the two interfaces and serves as their regression model. For a general CohFT, `ConnectedDegreeZero` produces its topological part, while `GenusZeroGeometry` supplies the low-genus facts used for Frobenius extraction and WDVV.

## Notes

- [Notes index](notes/README.md)
- [Mathematics-to-Lean map](notes/MathematicsToLean.md)
- [Implementation progress record](notes/milestones/ImplementationProgress.md)
- [The mathematics and goals of AxiomaticGW](notes/mathematics/ProjectMathematicsAndGoals.md)
- [The point target and stable-curve intersection theory](notes/mathematics/PointTargetAndStableCurves.md)
- [Mathematics notes for M1--M10](notes/mathematics/README.md)
- [Roadmap to axiomatic Gromov--Witten theory](notes/milestones/AxiomaticGWRoadmap.md)
- [Completed topological field theory milestones](notes/milestones/TopologicalTFTMilestones.md)

Build the project with:

```bash
lake build
```

## Contributing

Contributions to definitions, proofs, examples, documentation, and API design are welcome. Please read [CONTRIBUTING.md](CONTRIBUTING.md) and consult the [design-decision ledger](notes/milestones/CohFTDesignDecisions.md) before changing an unsettled architectural convention.

Before opening a pull request, run:

```bash
lake build
lake lint
lake test
git diff --check
```

Please report ordinary bugs and mathematical issues through GitHub Issues. Sensitive security reports should follow [SECURITY.md](SECURITY.md).

## License

AxiomaticGW is released under the [Apache License 2.0](LICENSE). Citation metadata is available in [CITATION.cff](CITATION.cff), and notable changes are recorded in [CHANGELOG.md](CHANGELOG.md).
