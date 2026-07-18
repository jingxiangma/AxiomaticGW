# Changelog

All notable user-visible changes to AxiomaticGW will be recorded here.

The project is research-stage and follows the pinned Lean/mathlib version in `lean-toolchain` and `lakefile.toml` rather than a stable compatibility policy.

## Unreleased

### Added

- Finite-free commutative Frobenius algebras and their canonical coalgebra.
- Basis-free copairing and named-slot contraction APIs.
- Finite-labelled all-genus topological correlators.
- Separating and nonseparating sewing theorems.
- Bundled topological correlator theories and scalar-valued topological CohFTs.
- Internally graded even-cohomology targets with primitive stable-curve pullbacks and coherence laws.
- Full cohomology-valued all-genus CohFTs and the optional `GradedCohFT`, `GenusZeroGeometry`, and `ConnectedDegreeZero` layers.
- Target-generic node contraction and tensor-valued separating contraction.
- The constant degree-zero target, forward/reverse topological CohFT conversion, and end-to-end regression tests.
- Degree-preserving stable-curve pullbacks and the immediate forget/glue coherence laws needed by the flat-unit and topological-part constructions.
- Genus-zero restriction, Frobenius extraction, metric invariance, WDVV, commutativity, unit laws, and associativity for full CohFTs.
- Coherent degree-zero scalarization and classification of every stable topological CohFT correlator by its extracted commutative Frobenius algebra.
- README-linked mathematics-to-Lean and implementation-progress records covering conceptual correspondence, milestone scope, verification evidence, and commit provenance.
- Stable-curve psi classes, integration, forgetful pushforward, kappa classes, and numerical ancestor correlators.
- Positive locally finite effective curve monoids and finite curve-class splitting sets.
- Graded, beta-resolved primary GW theories with virtual-degree, normalization, gluing, and optional divisor axioms, plus a beta-zero reference model.
- The beta-preserving Novikov completion with proven convolution ring laws, monomials, and an injective finite monoid-algebra inclusion.
- Fixed-beta three-point products with derived coefficientwise small WDVV, associativity, commutativity, and unit laws.
- Distinct stable-map descendant and stable-curve ancestor classes with a weak residual decomposition and an optional positive-degree rational-tail factorization package.
- Novikov-valued formal potentials, commuting formal partial derivatives with a Leibniz rule, Laurent total free energies, and separately usable stable string/dilaton and descendant divisor law interfaces.
- Descendant and ancestor potentials constructed from invariants, stable-sector and directional differential operators, and the potential-level descendant--ancestor residual identity.
- The invariant-defined commutative formal big quantum product and its proved zero-background specialization to the small product.
- Finite stable graphs with vertex stability, arithmetic genus, complete edge orders, and optional order-independent graph pullbacks.
- An explicit higher-background WDVV package deriving coefficientwise associativity of the formal big quantum product, together with the stable primary potential.
- Rational-tail stabilization data, a two-point calibration with a separately justified symplectic identity, and explicit coefficientwise Fock/quantized comparison carriers.
- Explicit unstable descendant conventions, a full descendant potential, and global correlator-level string and dilaton equations.
- A point-target stable-curve block with psi intersection numbers, dimension vanishing, initial values, a WDVV check, and the all-genus DVV proposition as an explicit geometric hypothesis.
- An abstract virtual-GW algebraic output carrier connecting future geometric constructions to the primary and descendant axiomatic layers; the carrier itself is not a realization theorem.
- Mathematical notes and a roadmap toward axiomatic Gromov--Witten theory.

### Fixed

- Corrected the forget/nonseparating and left forget/separating label transports in the stable-curve coherence axioms.
- Added the stable-curve top-degree bound, forgetful-pushforward relabelling and degree-zero laws, and derived kappa naturality and degree theorems.
- Corrected the stable-map descendant grading so cotangent powers contribute before testing whether the expected output degree is nonnegative.
- Added relabelling and total-degree theorems for ancestors and descendants, and derived the residual subtraction, relabelling, and homogeneity API.
- Replaced documentation claims of geometric boundary support and virtual realization with the weaker residual and carrier properties actually represented by the public API.
