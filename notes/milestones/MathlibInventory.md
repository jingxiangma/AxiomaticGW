# Mathlib dependency and project-ownership inventory

This note records which parts of M3--M10 are supplied by the pinned mathlib dependency and which parts belong to this project. It was checked against the source tree for mathlib `v4.32.0`, the revision in `lakefile.toml`, on 2026-07-16, and synchronized with the project implementation through commit `9a3d625` on 2026-07-18. The “must be built here” column is an ownership statement, not a current-status statement; each milestone section below distinguishes implemented project APIs from remaining gaps.

The distinction matters: a nearby general-purpose definition is not counted as an implementation of a GW-theoretic object. In particular, mathlib contains schemes, algebraic cycles, formal series, and graphs, but no stable-curve moduli spaces, CohFTs, or Gromov--Witten invariants.

## Summary

| Milestone | Reusable now | Must be built here |
| --- | --- | --- |
| M3 stable curves | Finite types and equivalences; multilinear relabelling; ordinary commutative graded-algebra/direct-sum infrastructure; tensor products; a looped multigraph type | The abstract even-cohomology stable-curve system, all geometric pullbacks and coherence laws, external products in the chosen target model, stable graphs and contraction/evaluation |
| M4 full CohFT | The project's perfect pairing, copairing, stable arities, and scalar contractions; mathlib multilinear maps and tensor products | Cohomology-valued contraction, the full CohFT record and axioms, the `(0,3)` and `(0,4)` target facts needed to extract the Frobenius algebra and prove associativity/WDVV |
| M5 tautological classes | Ordinary graded-ring operations; abstract linear maps; a very early scheme-level algebraic-cycle pushforward | Abstract pullback/pushforward/integration packages, projection/base-change formulas, `psi`, boundary, `kappa`, Hodge/`lambda` classes, and ancestor correlators |
| M6 curve classes | Commutative monoids, monoid homomorphisms, finite sums, gradings, and finite antidiagonals when an instance is available | The curve-class-resolved CohFT, finiteness of class splittings, virtual-dimension bookkeeping, divisor pairing/axiom, effectivity and degree-zero normalization |
| M7 Novikov/quantum | Finite monoid algebras; Hahn series under ordered-cancellative hypotheses; power and multivariate power series | The precise Novikov support condition or a justified Hahn-series specialization, coefficientwise-to-completed CohFT proofs, scalar extension, quantum products, WDVV |
| M8 descendants | General algebra, finite sums, and the M5 integration interface once built | Stable-map and ancestor psi classes as distinct data, stabilization/evaluation/virtual integration, boundary comparison, descendant invariants and the comparison theorem |
| M9 potentials | `PowerSeries`, `MvPowerSeries`, `LaurentSeries`, Hahn-series summability tools, factorials, exponentials, renaming and substitution | Multivariable formal partial derivatives, the mixed completion in all variables, genus/marking bookkeeping, equations, and a completion large enough for `exp(F)` when `F` starts with `hbar^-1` |
| M10 realization | Schemes and many morphism properties; fiber products; a basic `AlgebraicCycle` with quasicompact pushforward | Moduli stacks of curves/maps, Chow or suitable cohomology, rational equivalence, products and Gysin maps, Chern classes, perfect obstruction theories and virtual classes; initially, only an abstract virtual-GW interface should be attempted |

The realistic conclusion is that mathlib supplies most of the algebraic language but almost none of the GW-specific structures or geometric theorems. The repository now implements the stated axiomatic layers through M9, with explicit optional hypotheses where geometry is independent input. A first-principles M10 remains a separate large formalization project.

## Cross-cutting mathlib infrastructure

The following APIs are suitable foundations and should not be reimplemented.

- Finite labels: `Fintype`, `Finite`, `Equiv`, `Option`, `Sum`, `Finset`, and cardinality lemmas. The project already wraps the numerical stability condition in `AxiomaticGW.StableArity`.
- Multilinear algebra: `MultilinearMap`, `domDomCongr`, currying, coproducts of domains, `TensorProduct`, and `LinearMap`. The project contraction API specializes these tools to scalar- and target-valued correlators, including tensor-valued separating contraction.
- Internal gradings: `GradedRing`, `GradedAlgebra`, `DirectSum.Decomposition`, and `GradedAlgebra.proj` in `Mathlib.RingTheory.GradedAlgebra.Basic`.
- Tensor symmetry: ordinary `TensorProduct.comm` is sufficient for the chosen even-cohomology theory. Mathlib also has `TensorProduct.gradedComm`, but the project's CohFT interfaces do not need Koszul signs.
- Curve-class algebra: `AddMonoidAlgebra B R`/`MonoidAlgebra`, `Finsupp`, and `Finset.HasAntidiagonal`. The last is exactly the extra finiteness data needed to turn all decompositions `b1 + b2 = b` into a `Finset`.
- Formal coefficients: `PowerSeries`, `MvPowerSeries`, `LaurentSeries`, and `HahnSeries`. These are useful components, not by themselves the complete coefficient ring required by M7--M9.
- Graphs: `Graph V E` in `Mathlib.Combinatorics.Graph.Basic` is a multigraph allowing loops and parallel edges. It can underlie a stable-graph implementation, although its current API does not provide the needed legs, vertex genera, stability, edge contractions, or graph evaluation.
- Algebraic geometry: `AlgebraicGeometry.Scheme`, fiber products, and standard morphism properties including properness. `AlgebraicCycle X R` currently is a locally finitely supported function on scheme points and has a quasicompact-morphism pushforward `AlgebraicCycle.map`.

### Fixed grading convention for M3

The project restricts the stable-curve target to even cohomology. Thus each `H g S` is modeled as an ordinary commutative graded algebra, and relabelling, external products, and gluing carry no Koszul signs.

Use half the ordinary cohomological degree as the Lean grading:

```text
degree d  =  H^(2d)(Mbar(g,S)).
```

With this convention `psi` and divisor classes have degree one, multiplication adds degrees, and top degree agrees with complex dimension. Odd cohomology is outside the scope of the axiomatic interfaces rather than represented and forced to vanish.

## M3. Stable curves and gluing

### Already available

- The project's `StableArity` and its `Option`, separating, and nonseparating arithmetic lemmas.
- Arbitrary finite label types and transport along equivalences.
- Ring/algebra homomorphisms for contravariant pullbacks.
- Tensor products, direct sums, internal gradings, and ordinary tensor symmetry.
- A general multigraph carrier supporting loops and parallel edges.

### Project implementation and remaining gap

The project implements an abstract `StableCurveCohomology` record rather than constructing moduli spaces. The core supplies:

- a target `H g S` for every stable finite-labelled arity;
- an ordinary commutative algebra graded by half cohomological degree;
- relabelling, forgetful, separating-gluing, and nonseparating-gluing pullbacks;
- an external product or an equivalent bilinear map into the separating boundary target;
- functoriality, identity, naturality, the immediate forget/glue compatibility laws, and node/component symmetries;
- optional low-moduli-space input through `GenusZeroGeometry`, containing the point-like behavior of `Mbar(0,3)` and the boundary relation on `Mbar(0,4)`.

The separate `StableGraph` layer uses a purpose-built finite edge type with two branches. It implements labelled legs, vertex genera, vertex stability, relabelling, loop-aware valence, total genus, complete edge orders, and the optional `StableGraphPullbacks` package. Complete orders are permutation-equivalent, and the package yields a canonical order-independent pullback; the constant target supplies a concrete instance. Actual combinatorial edge contraction and a derivation of graph coherence solely from the primitive `StableCurveCohomology` laws are not implemented.

## M4. Full unital CohFT

### Already available

- `SymmetricPerfectPairing`, its canonical copairing, and finite-free module assumptions.
- `MultilinearMap` and the project's finite-label relabelling conventions.
- `selfContract` and `pairContract` for scalar-valued maps, together with target-generic and tensor-valued variants.
- `TopologicalCohFT`, which is a useful degree-zero test case for the new API.

### Project implementation

- Target-generic contraction and tensor-valued separating contraction combine cohomology-valued maps before contracting node inputs.
- `CohFT` records relabelling, flat unit, normalization, and both gluing axioms over `StableCurveCohomology`.
- Genus-zero restriction, degree-zero projection, Frobenius extraction, WDVV, and associativity are derived.
- `ConnectedDegreeZero` makes the connectedness hypothesis for scalar topological truncation explicit, and the classification theorem recovers every stable topological correlator.

There is no mathlib CohFT definition to adapt.

## M5. Tautological classes and ancestors

### Already available

Ordinary ring powers, graded components, linear maps, tensor products, and finite sums are ready. The new `AlgebraicCycle` API is relevant only to a much later scheme-level realization: it is not a Chow ring and does not supply the operations needed here.

### Project implementation and remaining gap

The implemented abstract intersection layer contains:

- stable-curve pullbacks, degree-shifting forgetful pushforward, and top-degree integration;
- relabelling naturality, degree laws, degree-zero vanishing, and the projection formula;
- marked classes `psi`, rational-tail boundary classes, and their forgetful correction formula;
- `kappa`, defined through pushforward, with degree and naturality theorems;
- dimension/top-degree vanishing sufficient to define numerical integrals;
- ancestor correlators and their symmetry/degree rules.

General pushforward composition and base change, Hodge/`lambda` classes, and decorated boundary-stratum classes remain absent because no current theorem consumes them. Mathlib `v4.32.0` has no general Chow ring, rational equivalence, cup/cap product package for these moduli spaces, applicable Chern-class package, or integration theorem.

## M6. Curve-class-resolved GW axioms

### Already available

- `AddCommMonoid B`, additive homomorphisms, submonoids, and ordered monoids.
- `Finsupp` and finite sums.
- `Finset.HasAntidiagonal B`, whose membership theorem identifies its entries with the splittings `b1 + b2 = b`.
- General grading and degree arithmetic.

### Project implementation

- `GromovWittenTheory` supplies coefficientwise classes `omega g S beta`, curve-class-resolved gluing, flat unit, normalization, and virtual-degree laws.
- `EffectiveCurveMonoid` stores positive locally finite energy data and derives finite splitting sets and a finite-antidiagonal interface.
- `GradedStateSpace` is reused by `GradedCohFT` and `GromovWittenTheory`; `c1Degree` records the Chern-number homomorphism.
- `GWDivisorAxiom` separately supplies divisor--curve pairing and forgetful pushforward because those are not consequences of the primary theory.

## M7. Novikov coefficients and quantum products

### Already available

- `AddMonoidAlgebra B R` gives the exact finite-support coefficient ring and is the right first backend for testing coefficientwise gluing.
- `HahnSeries B R` represents series with partially well-ordered support and has multiplication when `B` has the required ordered cancellative additive structure.
- Coefficient maps, monomials, finite-support embeddings, and summable-family tools exist for Hahn series.
- `PowerSeries` and `MvPowerSeries` can handle later formal insertions after a coefficient ring has been fixed.

### Project implementation and remaining gap

Decision D13 fixes a positive locally finite cancellative effective monoid `B` with additive energy in `ℕ`. The final coefficient type is the beta-preserving completed monoid ring of coefficient functions `B → R`, whose convolution is finite because bounded-energy sets and hence fixed antidiagonals are finite. `AddMonoidAlgebra B R` remains the finite-support subring and a useful regression backend. `HahnSeries` is not used because it would add a noncanonical order and PWO support obligations that the energy hypothesis makes unnecessary.

The project-owned objectives beyond the coefficient ring and their current boundaries are:

- monomial and coefficient lemmas matching curve-class splitting, implemented for `NovikovSeries` and the quantum-product coefficients;
- completed scalar and state-valued series where coefficientwise convolution is canonical, without claiming that arbitrary cohomology targets are algebraic scalar extensions;
- small-product WDVV and associativity derived from primitive coefficientwise gluing;
- the commutative big quantum product, its zero-background reduction, and associativity from optional genus-zero WDVV at arbitrary primary background;
- the still-open identification with an independently supplied classical cup product and the primary-potential third-derivative theorem.

The current implementation completes the coefficient ring and derives the small quantum product laws coefficientwise. `bigQuantumProduct` is commutative and specializes to the small quantum product at zero background. The optional `GenusZeroWDVV` states scalar genus-zero WDVV at arbitrary primary background and yields coefficientwise associativity; `primaryPotential` supplies the stable primary coefficients. Its full third-derivative characterization and an equality with an independently supplied classical cup product remain outside the present data.

## M8. Descendants and ancestor comparison

No GW-specific part of this milestone exists in mathlib. The reusable pieces are only the algebra and the abstract M5/M6 interfaces once those have been built.

The project owns distinct interfaces for stable-map `psi` and pulled-back stable-curve `psi`, together with descendant correlators and comparison data. The correction formula is an explicit theorem field of the optional stabilization package, never a definitional equality.

The current `DescendantAncestorComparison` remains only a residual decomposition. The optional `StabilizationBoundaryComparison` now meets the axiomatic comparison boundary by recording a finite positive-tail factorization and the associated two-point operators. Constructing that package from moduli-space geometry remains open.

The coefficientwise `TwoPointCalibration`, its separately assumed boundary identity, and an explicit quantized-action carrier are implemented. The repository does not claim an unrestricted exponential in the Laurent-series type.

## M9. All-genus potentials and equations

### Already available

- `MvPowerSeries Vars R` represents arbitrary-variable formal power series as coefficient functions on `Vars →₀ Nat` and supplies multiplication, coefficients, renaming, evaluation, and substitution.
- `PowerSeries` supplies one-variable derivatives and the universal exponential series over a rational algebra.
- `LaurentSeries R` is Hahn series with exponent group `Int`, appropriate for expressions with a uniform lower bound on powers of `hbar`.
- Hahn series has summable-family infrastructure.

### Project implementation and completion warning

- The project-owned `MvPowerSeries.pderiv` includes linearity, Leibniz, commutation, and iterated-derivative lemmas.
- `FormalPotential` nests formal insertion variables over `NovikovSeries`, while `totalFreeEnergy` uses a Laurent genus expansion; every completed convolution remains coefficientwise.
- Factorial denominators use `Algebra ℚ R` and the explicit `profileWeight` normalization.
- Stable string/dilaton and divisor laws are separate optional packages. `UnstableDescendantConventions` extends numerical correlators to all arities and derives global correlator-level string and dilaton equations.

Most importantly, `F = sum_g hbar^(g-1) F_g` is Laurent-bounded below by `-1`, but `exp(F)` generally contains arbitrarily negative powers of `hbar` because of powers of the genus-zero term. Decision D13 therefore leaves `exp(F)` outside the first axiomatic endpoint. M9 implements genus potentials and the honest Laurent-series total free energy; a mixed completion for the exponential will be introduced only when a concrete theorem consumes it.

Stable potentials retain their original convention; `fullDescendantPotential` uses the explicit unstable extension. A vector-field PDE presentation, the primary-potential third-derivative theorem, and the unrestricted exponential partition function remain unimplemented. `CompletedFockPotential` is only a coefficientwise carrier for an explicitly supplied quantized action, not the missing mixed exponential completion.

## M10. Geometric realization

### Already available

Mathlib has a substantial scheme layer: schemes, fiber products, many local and global morphism properties, and properness. The basic algebraic-cycle API defines cycles on schemes and a pushforward along quasicompact morphisms.

### Missing geometric foundations

The roadmap requires Deligne--Mumford or derived stacks, the actual moduli objects, a suitable cohomology or Chow theory with rational equivalence, products and refined Gysin pullbacks, Chern classes, perfect obstruction theories, intrinsic normal cones, virtual fundamental classes, and their gluing/base-change compatibility. These are not present in mathlib `v4.32.0`. The existing scheme `AlgebraicCycle` is an early building block, not a substitute for them.

Accordingly, the current M10 deliverable is only an abstract `VirtualGWPackage` carrier whose fields store already axiomatized M6 and M8 outputs, followed by projections such as

```text
VirtualGWPackage -> GromovWittenTheory.
```

This is not a realization construction and does not encode boundary support for the descendant--ancestor residual. Constructing a concrete instance from moduli stacks and virtual classes should remain explicitly out of scope until those external foundations exist.

## Recommended implementation gates

1. **M3a (complete):** implement the even-cohomology targets, graded by half cohomological degree, and the primitive stable-curve pullbacks with coherence.
2. **M4a (complete):** generalize contraction to arbitrary codomains and define full CohFT; use the existing topological theory as the first instance.
3. **M3b/M4b (complete):** retain only the `Mbar(0,3)` and `Mbar(0,4)` facts in the core; use the separate optional stable-graph layer for iterated gluing.
4. **M5 (complete core):** add abstract intersection operations and tautological data.
5. **M6 (complete core):** require finite class antidiagonals and settle grading conventions.
6. **M7a (complete):** implement the finite-support inclusion and completed Novikov coefficient ring.
7. **M7b/M9a (complete for the current endpoint):** prove the beta-preserving convolution ring and the Laurent-bounded total free energy.
8. **M8/M9 (complete axiomatic layer):** descendant families, rational-tail comparison data, stable/full generating functions, and global correlator equations are implemented as explicit optional packages.
9. **M10 (carrier only):** retain the algebraic output carrier while recording that a realization theorem requires external geometric foundations.
