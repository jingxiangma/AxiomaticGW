# Roadmap from foundations to axiomatic Gromov--Witten theory

This document gives the rough implementation order for the whole project. Detailed definitions and completion criteria belong in separate milestone notes when a phase becomes active.

For an audit of reusable APIs in the pinned mathlib revision, project ownership, implemented layers, and remaining geometric gaps, see the [mathlib inventory for M3--M10](MathlibInventory.md). The settled architectural choices and their implementation consequences are tracked in the [CohFT design-decision ledger](CohFTDesignDecisions.md).

The [mathematics-to-Lean map](../MathematicsToLean.md) records the correspondence between mathematical sections and implemented modules. Completed scope, verification evidence, and commit provenance are recorded in the [implementation progress record](ImplementationProgress.md).

The intended endpoint is an all-genus, curve-class-resolved axiomatic Gromov--Witten theory with primary classes, descendants, ancestors, Novikov coefficients, genus potentials, and total free energies.

## M0. Project foundations

Set up the Lean project, source layout, documentation conventions, tests, and local Git workflow.

**Status:** Complete.

## M1. Perfect pairings and Frobenius algebras

[Mathematical background](../mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md)

Formalize symmetric perfect pairings, the canonical copairing, commutative Frobenius algebras, their coalgebra structure, and the handle element.

**Status:** Complete.

## M2. Two-dimensional topological field theory

[Mathematical background](../mathematics/M02TwoDimensionalTFT.md)

Construct finite-labelled all-genus correlators, prove separating and nonseparating sewing, bundle the two-dimensional TFT, and obtain its scalar-valued topological CohFT restriction.

**Status:** Complete for the current fixed-algebra API.

## M3. Stable curves and gluing

[Mathematical background](../mathematics/M03StableCurvesAndGluing.md)

Introduce an abstract even-cohomology system for stable-curve moduli spaces, modeled by ordinary commutative algebras graded by half cohomological degree. Include finite-label relabelling, forgetful maps, separating gluing, nonseparating gluing, and the compatibility identities needed by CohFTs. Add optional `GenusZeroGeometry` and `ConnectedDegreeZero` extensions for the special low-genus relations and the identifications $H^0(\overline{\mathcal M}_{g,S})\cong R$. Keep stable graphs in a separate layer for iterated gluing data; actual combinatorial edge contraction is not part of the current layer. Odd cohomology and Koszul signs are outside the project scope.

**Status:** Complete for the primitive-map interface fixed by D9. All maps are degree-preserving, the immediate forget/glue coherence laws are present, and the constant model validates the interface. The separate stable-graph layer now provides finite stable graphs, vertex factors, arithmetic genus, complete edge orders, and optional order-independent graph pullbacks without strengthening `StableCurveCohomology`.

## M4. Full unital CohFT

[Mathematical background](../mathematics/M04FullUnitalCohFT.md)

Define a CohFT simultaneously for every stable genus and label set. Prove that its three-point genus-zero part gives a Frobenius algebra, define its topological part, and derive the genus-zero restriction, associativity, and WDVV from the all-genus theory. Frobenius extraction and WDVV use `GenusZeroGeometry`; scalar-valued topological truncation uses `ConnectedDegreeZero`.

M3/M4 are accepted only after the constant degree-zero cohomology system is implemented, contraction works with arbitrary target modules, the existing `TopologicalCohFT` converts to the full CohFT over that system, and representative relabelling, unit, separating, nonseparating, and topological truncation tests pass.

**Status:** Complete. The implementation includes the genus-zero restriction, Frobenius extraction, metric invariance, WDVV, commutativity, unit and associativity, general degree-zero topological truncation, and the full stable-arity classification of topological CohFTs by the extracted Frobenius algebra.

## M5. Tautological classes and ancestors

[Mathematical background](../mathematics/M05TautologicalClassesAndAncestors.md)

Extend the stable-curve system with `psi`, `kappa`, and Hodge classes where needed, together with integration, pushforward, and projection formulas. Use stable-curve `psi`-classes to define ancestor correlators and their basic relations.

**Status:** Complete for the current ancestor layer and for the first combinatorial strata layer. `PsiClasses`, top-degree integration, forgetful pushforward with relabelling naturality, degree shift, degree-zero vanishing and projection formula, the rational-tail forgetful correction, kappa degree/naturality, and numerical ancestors are implemented, with a constant-target regression model. Decorated stable graphs modulo isomorphism, codimension, one-vertex strata, the free rational strata module, dimension and supplied-relation quotients, a degree-preserving realization adapter, the exact named Getzler relation, and low-genus genus-zero psi values are also implemented. The strata product is currently a certified contract rather than a common-refinement algorithm. General pushforward composition and base change, Hodge classes, native product enumeration, explicit normalized Getzler graph cycles, geometric relation proofs, and a concrete stable-curve cohomology realization remain open.

## M6. Curve-class-resolved GW axioms

[Mathematical background](../mathematics/M06CurveClassResolvedGW.md)

Add a positive locally finite cancellative effective curve-class monoid and classes

$$
\Omega_{g,S,\beta}:V^{\otimes S}\longrightarrow
H^*(\overline{\mathcal M}_{g,S}).
$$

Formalize symmetry, the flat unit, splitting, genus reduction, grading, virtual dimension, effectivity, divisor data, and the appropriate degree-zero normalizations.

`GradedStateSpace` factors the state-space grading, homogeneous unit, and degree compatibility of the pairing out of `GradedCohFT`. The coefficientwise `GromovWittenTheory` structure reuses that data without pretending that an arbitrary cohomology target admits an algebraic Novikov scalar extension; its `beta`-dependent virtual-dimension law belongs specifically to the GW layer.

**Status:** Complete for the primary axiomatic core. Positive locally finite effective classes, finite splittings, graded primary classes, relabelling, unit, separating and nonseparating gluing, normalization, virtual degree, negative-degree vanishing, and the optional primary divisor axiom are implemented. The beta-zero base-ring theory is the regression model.

## M7. Novikov coefficients and quantum products

[Mathematical background](../mathematics/M07NovikovAndQuantumProducts.md)

Package the coefficientwise curve-class theory using the beta-preserving completed monoid ring fixed by D13. Define small and big quantum products and prove associativity and WDVV.

**Status:** Complete for the coefficientwise scope fixed by D14. `NovikovSeries` is the beta-preserving completed monoid ring, with proven commutative-ring laws, monomial multiplication, and an injective finite monoid-algebra map. Fixed-beta products and small associativity are derived directly from `GromovWittenTheory` gluing. The big quantum product is commutative and specializes to the small quantum product; the optional `GenusZeroWDVV` supplies scalar genus-zero WDVV at arbitrary primary background and yields coefficientwise associativity. The stable primary potential is defined, while its full formal third-derivative characterization remains open.

## M8. Descendants and descendant--ancestor comparison

[Mathematical background](../mathematics/M08DescendantsAndAncestors.md)

Introduce stable-map `psi`-classes separately from stable-curve `psi`-classes. Define descendant correlators and prove the comparison with ancestors once the necessary stabilization and boundary formulas are available.

**Status:** Complete as an optional axiomatic comparison. Stable-map descendant classes remain separate from stable-curve `PsiClasses`. `DescendantAncestorComparison` is the weak residual API; `StabilizationBoundaryComparison` adds explicit positive-degree rational-tail support, factorized boundary data, and the two-point tail operators used by the calibration. Symplecticity and the coefficientwise descendant--ancestor identity require separately named optional boundary/Fock hypotheses. Concrete stable-map geometry has not yet constructed these packages.

## M9. All-genus potentials and equations

[Mathematical background](../mathematics/M09PotentialsAndEquations.md)

Define genus expansions, descendant and ancestor genus potentials, and their total free energies. Prove string, dilaton, divisor, splitting, genus-reduction, and tautological relations from the corresponding abstract axioms. The exponential total potential is deferred until a theorem requires a mixed completion supporting its unbounded negative `hbar` powers.

**Status:** Complete for stable potentials and explicit unstable extensions. Stable-sector descendant and ancestor potentials, formal derivatives, Laurent total free energies, and the residual identity are implemented. `UnstableDescendantConventions` supplies the missing arities without asserting geometric vanishing, and stable plus exceptional recurrences derive global correlator-level string and dilaton equations and `fullDescendantPotential`. A vector-field PDE presentation and unrestricted exponential total potential remain deliberately deferred.

## M10. Geometric realization

[Mathematical background](../mathematics/M10GeometricRealization.md)

Expose an algebraic output carrier for a future virtual stable-map construction: the primary theory, stabilized descendants, and their residual decomposition against ancestors. A future geometric refinement must strengthen and construct this data from evaluation maps, stabilization, virtual classes, pullbacks, pushforwards, and virtual gluing. Constructing actual moduli stacks and virtual fundamental classes is a later, substantially larger geometric project.

**Status:** Algebraic carrier implemented; realization not implemented. `VirtualGWPackage` bundles already axiomatized primary, descendant, and residual data. Its projections do not certify a virtual-geometric origin or boundary support. Constructing and validating such data from actual moduli stacks and virtual fundamental classes remains a separate geometric formalization project.

## Dependency summary

```text
project setup
  -> perfect pairings and Frobenius algebras
  -> 2D topological field theory
  -> stable-curve gluing system
  -> full all-genus CohFT
  -> tautological and ancestor theory
  -> curve-class-resolved GW axioms
  -> Novikov coefficients and quantum products
  -> descendants and descendant--ancestor comparison
  -> all-genus potentials and equations
  -> optional geometric realization
```
