# AxiomaticGW

Lean formalization of the algebraic foundations of axiomatic Gromov--Witten theory.

The repository is the home of the full project, but development proceeds in small verified milestones. The finite-free commutative Frobenius-algebra and coalgebra layer, its finite-labelled topological correlator theory, and its scalar-valued topological CohFT restriction are now implemented. The next major phase is the abstract stable-curve cohomology and full CohFT interface.

> **Project status:** active, research-stage development. The implemented
> foundations compile without `sorry` or `admit`; planned APIs may still change
> before a stable release.

## Getting started

Install Lean with [elan](https://github.com/leanprover/elan), clone the
repository, and run:

```bash
lake exe cache get
lake build
lake test
```

The project pins Lean and mathlib to `v4.32.0`. Import the current public API
with:

```lean
import AxiomaticGW
```

Run `lake lint` before submitting changes. CI performs the build, test, and
lint steps on every pull request to `main`.

## Final scope

The endpoint is an **all-genus axiomatic Gromov--Witten theory**, resolved by curve class and equipped with the complete descendant package. In particular, the final theory is intended to support

- primary GW classes for every stable `(g, S)` and every effective curve class;
- separating and nonseparating gluing, the flat unit, grading, virtual dimension, effectivity, and the divisor axiom;
- descendant insertions indexed by arbitrary powers of stable-map `psi`-classes;
- ancestor insertions using stable-curve `psi`-classes, together with the descendant--ancestor comparison;
- Novikov completion and genus expansion;
- all-genus descendant and ancestor potentials;
- string, dilaton, divisor, splitting, genus-reduction, and tautological relations whenever the required abstract geometric operations are present.

A bare CohFT already contains all stable genera. The genus-zero API is only a derived restriction used to prove associativity and WDVV. Descendants are not fields of the minimal CohFT structure: they require `psi`-classes, pushforwards, integration, and projection formulas. Moreover, stable-map descendants and stable-curve ancestors are kept distinct.

## Architecture

The intended dependency direction is

```text
                         Combinatorics
                        /             \
Mathlib -> Linear -> Frobenius -> TFT  \
                \                       -> CohFT -> GW -> Geometry
                 -> Coefficients       /
                \                     /
                 -> Moduli -----------
```

The planned source layout is:

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
    FiniteLabels.lean
    StableGraph.lean
    GraphContraction.lean

  Coefficients/
    EffectiveCurveClass.lean
    Novikov.lean
    GenusExpansion.lean
    DescendantVariables.lean

  Moduli/
    StableCurveSystem.lean
    Gluing.lean
    TautologicalSystem.lean
    Integration.lean

  CohFT/
    Topological.lean           # implemented scalar-valued stable theory
    Basic.lean                 # full all-genus CohFT
    Unit.lean
    GenusZero.lean             # restriction of the all-genus theory
    Frobenius.lean
    TopologicalPart.lean
    Ancestors.lean             # stable-curve psi-classes
    Potential.lean

  GW/
    CurveClass.lean
    Basic.lean                 # beta-resolved, full all-genus primary theory
    Grading.lean
    Divisor.lean
    Novikov.lean
    QuantumProduct.lean
    Ancestors.lean
    Descendants/
      Basic.lean               # stable-map psi insertions
      Axioms.lean
      Comparison.lean          # descendants versus ancestors
      Potential.lean           # all-genus total descendant potential

  Geometry/
    StableMapSystem.lean
    VirtualGWPackage.lean
    Realization.lean

  Examples/
    Point.lean
    FrobeniusTFT.lean
    ProjectiveLine.lean
```

Only modules with implemented content are created. The tree above records ownership and dependency boundaries without committing prematurely to Lean interfaces that have not yet been tested.

The essential formalization chain is

```text
perfect duality and contractions
  -> Frobenius algebra and topological CohFT
  -> full all-genus CohFT
  -> beta-resolved all-genus primary GW theory
  -> Novikov-valued CohFT and quantum products
  -> full descendants, ancestors, comparison, and total potentials
  -> realization from an abstract virtual stable-map package
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
  -> recovery of the counit and three-point product.
```

The geometric oriented bordism category is not formalized: `TopologicalCorrelatorTheory` is its algebraic correlator presentation. Likewise, `TopologicalCohFT` is currently scalar-valued and models degree-zero classes. The next major milestone replaces those scalars with an abstract cohomology system for stable curves and then defines a full all-genus CohFT.

## Notes

- [Notes index](notes/README.md)
- [The mathematics and goals of AxiomaticGW](notes/mathematics/ProjectMathematicsAndGoals.md)
- [Mathematics notes for M1--M10](notes/mathematics/README.md)
- [Roadmap to axiomatic Gromov--Witten theory](notes/milestones/AxiomaticGWRoadmap.md)
- [Completed topological field theory milestones](notes/milestones/TopologicalTFTMilestones.md)

Build the project with:

```bash
lake build
```

## Contributing

Contributions to definitions, proofs, examples, documentation, and API design
are welcome. Please read [CONTRIBUTING.md](CONTRIBUTING.md) and consult the
[design-decision ledger](notes/milestones/CohFTDesignDecisions.md) before
changing an unsettled architectural convention.

Before opening a pull request, run:

```bash
lake build
lake lint
lake test
git diff --check
```

Please report ordinary bugs and mathematical issues through GitHub Issues.
Sensitive security reports should follow [SECURITY.md](SECURITY.md).

## License

AxiomaticGW is released under the [Apache License 2.0](LICENSE). Citation
metadata is available in [CITATION.cff](CITATION.cff), and notable changes are
recorded in [CHANGELOG.md](CHANGELOG.md).
