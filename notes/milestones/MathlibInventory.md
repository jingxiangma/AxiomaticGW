# Mathlib inventory for future milestones

This note records which parts of M3--M10 are supplied by the pinned mathlib dependency and which parts must be implemented in this project. It was checked against the source tree for mathlib `v4.32.0`, the revision in `lakefile.toml`, on 2026-07-16.

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

The realistic conclusion is that mathlib supplies most of the algebraic language but almost none of the GW-specific structures or geometric theorems. M3--M9 remain feasible as an axiomatic development. A first-principles M10 is a separate large formalization project.

## Cross-cutting mathlib infrastructure

The following APIs are suitable foundations and should not be reimplemented.

- Finite labels: `Fintype`, `Finite`, `Equiv`, `Option`, `Sum`, `Finset`, and cardinality lemmas. The project already wraps the numerical stability condition in `AxiomaticGW.StableArity`.
- Multilinear algebra: `MultilinearMap`, `domDomCongr`, currying, coproducts of domains, `TensorProduct`, and `LinearMap`. The existing project contraction API specializes these tools to scalar-valued correlators.
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

### Required implementation

The first deliverable should be an abstract `StableCurveCohomology`-style record, not a construction of moduli spaces. It needs:

- a target `H g S` for every stable finite-labelled arity;
- an ordinary commutative algebra graded by half cohomological degree;
- relabelling, forgetful, separating-gluing, and nonseparating-gluing pullbacks;
- an external product or an equivalent bilinear map into the separating boundary target;
- functoriality, identity, naturality, forget/glue compatibility, and commutation of disjoint gluings;
- explicit low-moduli-space input: the point-like behavior of `Mbar(0,3)` and the equality/boundary relation on `Mbar(0,4)` needed later.

Stable graphs should be a second layer. `Graph V E` may be reused for internal edges, but the project must add finite legs/half-edges, leg labels, vertex genera, vertex stability, total genus, contraction, and independence of edge contraction order. A purpose-built finite half-edge record may be easier than forcing all decorations through the general embedded-set graph API.

## M4. Full unital CohFT

### Already available

- `SymmetricPerfectPairing`, its canonical copairing, and finite-free module assumptions.
- `MultilinearMap` and the project's finite-label relabelling conventions.
- `selfContract` and `pairContract` for scalar-valued maps.
- `TopologicalCohFT`, which is a useful degree-zero test case for the new API.

### Required implementation

- Generalize contraction from codomain `R` to a target module/algebra `H`. Separating contraction must combine two cohomology-valued maps using the external product before contracting the two state-space inputs.
- Define the full cohomology-valued CohFT record over the M3 system, including relabelling, flat unit, normalization, and both gluing axioms.
- Define restriction to genus zero and projection to degree zero.
- Extract the three-point product. Proving its laws is not purely multilinear algebra: commutativity uses relabelling, the unit uses the forgetful axiom, and associativity/WDVV needs the M3 `Mbar(0,4)` relation.
- Prove that the degree-zero theory agrees with the existing topological CohFT only under an explicit connectedness/degree-zero-target hypothesis.

There is no mathlib CohFT definition to adapt.

## M5. Tautological classes and ancestors

### Already available

Ordinary ring powers, graded components, linear maps, tensor products, and finite sums are ready. The new `AlgebraicCycle` API is relevant only to a much later scheme-level realization: it is not a Chow ring and does not supply the operations needed here.

### Required implementation

Extend M3 with an abstract bivariant/intersection package containing:

- pullback, degree-shifting proper pushforward, external products, and integration;
- functoriality, projection formula, the required base-change identities, and compatibility with gluing;
- marked classes `psi`, rational-tail boundary classes and their forgetful correction formula;
- `kappa` (possibly defined through pushforward), Hodge/`lambda` classes, and boundary-stratum classes;
- dimension/top-degree vanishing sufficient to define numerical integrals;
- ancestor correlators and their symmetry/degree rules.

Mathlib `v4.32.0` has no general Chow ring, rational equivalence, cup/cap product package for these moduli spaces, Chern-class package applicable here, or integration theorem. These should be fields and laws of the abstract M5 interface rather than blocked on geometric foundations.

## M6. Curve-class-resolved GW axioms

### Already available

- `AddCommMonoid B`, additive homomorphisms, submonoids, and ordered monoids.
- `Finsupp` and finite sums.
- `Finset.HasAntidiagonal B`, whose membership theorem identifies its entries with the splittings `b1 + b2 = b`.
- General grading and degree arithmetic.

### Required implementation

- A coefficientwise class `omega g S beta` extending M4.
- A stated finiteness hypothesis for separating sums. Prefer `[Finset.HasAntidiagonal B]` in the first algebraic API, or store finite splitting data explicitly. An arbitrary commutative monoid is not enough.
- Curve-class-resolved separating and nonseparating axioms.
- A grading convention for the state space and target, plus a checked virtual dimension/degree formula.
- The Chern-number/energy homomorphism on curve classes and the divisor--curve pairing as additional data.
- Flat unit, divisor pushforward, effectivity (if indexing a group), and separate genus-zero and higher-genus degree-zero normalizations.

The current state space is ungraded, so M6 requires either a graded state-space extension or an explicit degree predicate on homogeneous insertions.

## M7. Novikov coefficients and quantum products

### Already available

- `AddMonoidAlgebra B R` gives the exact finite-support coefficient ring and is the right first backend for testing coefficientwise gluing.
- `HahnSeries B R` represents series with partially well-ordered support and has multiplication when `B` has the required ordered cancellative additive structure.
- Coefficient maps, monomials, finite-support embeddings, and summable-family tools exist for Hahn series.
- `PowerSeries` and `MvPowerSeries` can handle later formal insertions after a coefficient ring has been fixed.

### Required implementation and choice

The project must first state its Novikov convention. Two viable stages are:

1. Prove all constructions over `AddMonoidAlgebra B R` under finite total support. This isolates CohFT algebra from completion issues.
2. Use `HahnSeries B R` under explicit order/cancellation hypotheses, proving that the chosen energy-local-finiteness condition implies its PWO support; or define a custom energy-filtered `NovikovSeries B R E` subtype.

Using `HahnSeries (range E) R` alone is generally wrong because distinct curve classes with the same energy would be merged. Indexing Hahn series by `B` preserves coefficients but requires an appropriate compatible order on `B`.

Beyond the coefficient ring, build:

- monomial and coefficient lemmas matching curve-class splitting;
- scalar extension of the state space, metric, cohomology targets, and multilinear classes;
- the theorem turning coefficientwise gluing into ordinary completed gluing;
- small and big quantum products and associativity/WDVV;
- the classical-limit theorem at curve class zero.

## M8. Descendants and ancestor comparison

No GW-specific part of this milestone exists in mathlib. The reusable pieces are only the algebra and the abstract M5/M6 interfaces once those have been built.

The project must add distinct types or namespaces for stable-map `psi` and pulled-back stable-curve `psi`, along with stabilization, evaluation insertions, virtual integration/pushforward, forgetful and boundary formulas, descendant correlators, and the comparison theorem. The correction formula must be a theorem/axiom of this package, never definitional equality.

The generating-function `S`-operator should wait until the coefficient and formal-series choices of M7 and M9 are stable.

## M9. All-genus potentials and equations

### Already available

- `MvPowerSeries Vars R` represents arbitrary-variable formal power series as coefficient functions on `Vars →₀ Nat` and supplies multiplication, coefficients, renaming, evaluation, and substitution.
- `PowerSeries` supplies one-variable derivatives and the universal exponential series over a rational algebra.
- `LaurentSeries R` is Hahn series with exponent group `Int`, appropriate for expressions with a uniform lower bound on powers of `hbar`.
- Hahn series has summable-family infrastructure.

### Required implementation and completion warning

- Mathlib currently has no formal partial derivative API for `MvPowerSeries`; define coefficientwise `pderiv` and its linearity, Leibniz, commutation, and iterated-derivative lemmas.
- Choose a single mixed coefficient type for Novikov, descendant variables, and genus. Nesting existing series types may work for individual free energies, but every interchange of sums needs a support theorem.
- Encode factorial denominators with assumptions such as `Algebra ℚ R`, or use divided-power coefficients to support more general base rings.
- Formalize stable/unstable conventions and prove string, dilaton, divisor, splitting, genus-reduction, WDVV, and tautological equations at the coefficient level before translating them to differential equations.

Most importantly, `F = sum_g hbar^(g-1) F_g` is Laurent-bounded below by `-1`, but `exp(F)` generally contains arbitrarily negative powers of `hbar` because of powers of the genus-zero term. Thus the total descendant potential is not, in general, an ordinary `LaurentSeries` in `hbar`. M9 must either:

- keep `D = exp(F)` as a symbolic exponential;
- impose an additional filtration in the insertion/Novikov variables and use a two-dimensional completion; or
- define the total potential coefficientwise in that filtration.

This completion decision should be made before implementing big quantum products, not postponed to the end of M9.

## M10. Geometric realization

### Already available

Mathlib has a substantial scheme layer: schemes, fiber products, many local and global morphism properties, and properness. The basic algebraic-cycle API defines cycles on schemes and a pushforward along quasicompact morphisms.

### Missing geometric foundations

The roadmap requires Deligne--Mumford or derived stacks, the actual moduli objects, a suitable cohomology or Chow theory with rational equivalence, products and refined Gysin pullbacks, Chern classes, perfect obstruction theories, intrinsic normal cones, virtual fundamental classes, and their gluing/base-change compatibility. These are not present in mathlib `v4.32.0`. The existing scheme `AlgebraicCycle` is an early building block, not a substitute for them.

Accordingly, the achievable M10 deliverable in this repository is an abstract `VirtualGWPackage` whose fields expose precisely the operations and theorems used in M5, M6, and M8, followed by a construction

```text
VirtualGWPackage -> CurveClassResolvedGWTheory.
```

Constructing a concrete instance from moduli stacks and virtual classes should remain explicitly out of scope until those external foundations exist.

## Recommended implementation gates

1. **M3a (complete):** implement the even-cohomology targets, graded by half cohomological degree, and the primitive stable-curve pullbacks with coherence.
2. **M4a (complete):** generalize contraction to arbitrary codomains and define full CohFT; use the existing topological theory as the first instance.
3. **M3b/M4b (complete):** add only the `Mbar(0,3)` and `Mbar(0,4)` facts needed for the Frobenius/WDVV theorems; defer general stable graphs.
4. **M5:** add abstract intersection operations and tautological data.
5. **M6:** require finite class antidiagonals and settle grading conventions.
6. **M7a:** implement the finite monoid-algebra theory first.
7. **M7b/M9a:** choose and prove the Novikov and mixed formal completions.
8. **M8/M9:** add descendants and equations coefficientwise, then package generating functions.
9. **M10:** define only the abstract realization interface unless mathlib's geometric foundations change substantially.
