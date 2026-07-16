# Roadmap from foundations to axiomatic Gromov--Witten theory

This document gives the rough implementation order for the whole project.
Detailed definitions and completion criteria belong in separate milestone notes
when a phase becomes active.

For an audit of reusable APIs in the pinned mathlib revision and the structures
that still need to be implemented, see the
[mathlib inventory for M3--M10](MathlibInventory.md).
The architectural choices to settle before implementation are tracked in the
[CohFT design-decision ledger](CohFTDesignDecisions.md).

The intended endpoint is an all-genus, curve-class-resolved axiomatic
Gromov--Witten theory with primary classes, descendants, ancestors, Novikov
coefficients, and total potentials.

## M0. Project foundations

Set up the Lean project, source layout, documentation conventions, tests, and
local Git workflow.

**Status:** Complete.

## M1. Perfect pairings and Frobenius algebras

[Mathematical background](../mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md)

Formalize symmetric perfect pairings, the canonical copairing, commutative
Frobenius algebras, their coalgebra structure, and the handle element.

**Status:** Complete.

## M2. Two-dimensional topological field theory

[Mathematical background](../mathematics/M02TwoDimensionalTFT.md)

Construct finite-labelled all-genus correlators, prove separating and
nonseparating sewing, bundle the topological correlator theory, and obtain its
scalar-valued topological CohFT restriction.

**Status:** Complete for the current fixed-algebra API.

## M3. Stable curves and gluing

[Mathematical background](../mathematics/M03StableCurvesAndGluing.md)

Introduce an abstract even-cohomology system for stable-curve moduli spaces,
modeled by ordinary commutative algebras graded by half cohomological degree.
Include finite-label relabelling, forgetful maps, separating gluing,
nonseparating gluing, and the compatibility identities needed by CohFTs.
Stable graphs and graph contraction can then package iterated gluing. Odd
cohomology and Koszul signs are outside the project scope.

**Status:** Next major phase.

## M4. Full unital CohFT

[Mathematical background](../mathematics/M04FullUnitalCohFT.md)

Define a CohFT simultaneously for every stable genus and label set. Prove that
its three-point genus-zero part gives a Frobenius algebra, define its
topological part, and derive the genus-zero restriction, associativity, and
WDVV from the all-genus theory.

**Status:** Planned.

## M5. Tautological classes and ancestors

[Mathematical background](../mathematics/M05TautologicalClassesAndAncestors.md)

Extend the stable-curve system with `psi`, `kappa`, and Hodge classes where
needed, together with integration, pushforward, and projection formulas. Use
stable-curve `psi`-classes to define ancestor correlators and their basic
relations.

**Status:** Planned.

## M6. Curve-class-resolved GW axioms

[Mathematical background](../mathematics/M06CurveClassResolvedGW.md)

Add an effective curve-class monoid and classes

$$
\Omega_{g,S,\beta}:V^{\otimes S}\longrightarrow
H^*(\overline{\mathcal M}_{g,S}).
$$

Formalize symmetry, the flat unit, splitting, genus reduction, grading, virtual
dimension, effectivity, divisor data, and the appropriate degree-zero
normalizations.

**Status:** Planned.

## M7. Novikov coefficients and quantum products

[Mathematical background](../mathematics/M07NovikovAndQuantumProducts.md)

Package the coefficientwise curve-class theory as a Novikov-valued CohFT under
the required finiteness or completion hypotheses. Define small and big quantum
products and prove associativity and WDVV.

**Status:** Planned.

## M8. Descendants and descendant--ancestor comparison

[Mathematical background](../mathematics/M08DescendantsAndAncestors.md)

Introduce stable-map `psi`-classes separately from stable-curve `psi`-classes.
Define descendant correlators and prove the comparison with ancestors once the
necessary stabilization and boundary formulas are available.

**Status:** Planned.

## M9. All-genus potentials and equations

[Mathematical background](../mathematics/M09PotentialsAndEquations.md)

Define genus expansions and the total descendant and ancestor potentials.
Prove string, dilaton, divisor, splitting, genus-reduction, and tautological
relations from the corresponding abstract axioms.

**Status:** Planned. Completion of this phase is the main axiomatic GW endpoint.

## M10. Geometric realization

[Mathematical background](../mathematics/M10GeometricRealization.md)

Specify an abstract virtual stable-map package with evaluation maps,
stabilization, virtual classes, pullbacks, pushforwards, and virtual gluing.
Prove that every such package produces the axiomatic GW theory developed above.
Constructing actual moduli stacks and virtual fundamental classes is a later,
substantially larger geometric project.

**Status:** Optional extension beyond the first axiomatic endpoint.

## Dependency summary

```text
project setup
  -> perfect pairings and Frobenius algebras
  -> 2D topological field theory
  -> stable-curve gluing system
  -> full all-genus CohFT
  -> tautological and ancestor theory
  -> curve-class-resolved GW axioms
  -> Novikov CohFT and quantum products
  -> descendants and descendant--ancestor comparison
  -> all-genus potentials and equations
  -> optional geometric realization
```
