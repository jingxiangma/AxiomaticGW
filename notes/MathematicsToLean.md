# Mathematics-to-Lean map

This file is the canonical bridge between the mathematical exposition and the Lean implementation. It maps implemented mathematical sections to source modules and principal declarations, and it states explicitly when a mathematical topic is intentionally not yet formalized.

The [implementation progress record](milestones/ImplementationProgress.md) contains dated scope, commit provenance, and verification evidence. Generated API documentation remains the declaration-level reference; this map explains where the mathematics enters that API.

## M1. Perfect pairings and Frobenius algebras

**Mathematical note:** [M1. Perfect pairings and Frobenius algebras](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md).

- [Algebraic setting](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md#1-algebraic-setting) and [commutative Frobenius algebras](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md#2-commutative-frobenius-algebras) correspond to [`Frobenius/Basic.lean`](../AxiomaticGW/Frobenius/Basic.lean), principally `tracePairing`, `CommFrobeniusAlgebra`, `CommFrobeniusAlgebra.pairing`, and `pairing_assoc`.
- [Copairing and contraction](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md#3-copairing-and-contraction) correspond to [`Linear/PerfectPairing.lean`](../AxiomaticGW/Linear/PerfectPairing.lean), [`Linear/Copairing.lean`](../AxiomaticGW/Linear/Copairing.lean), and [`Linear/Contraction.lean`](../AxiomaticGW/Linear/Contraction.lean), principally `SymmetricPerfectPairing`, `toDual`, `copairing`, `contractTwo`, `selfContract`, and `pairContract`.
- [Coalgebra structure](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md#4-coalgebra-structure) corresponds to [`Frobenius/Constructions.lean`](../AxiomaticGW/Frobenius/Constructions.lean) and [`Frobenius/Coalgebra.lean`](../AxiomaticGW/Frobenius/Coalgebra.lean), principally `casimir`, `handleElement`, `comul`, `coassoc`, `toCoalgebra`, and `toIsCocomm`.
- [Examples](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md#5-examples) correspond to [`Frobenius/Examples.lean`](../AxiomaticGW/Frobenius/Examples.lean), including `baseRing` and `productAlgebra`. The dual-number example remains mathematical only.

## M2. Two-dimensional topological field theory

**Mathematical note:** [M2. Two-dimensional topological field theory](mathematics/M02TwoDimensionalTFT.md).

- [Bordisms and field theories](mathematics/M02TwoDimensionalTFT.md#1-bordisms-and-field-theories) are represented algebraically by [`TFT/Basic.lean`](../AxiomaticGW/TFT/Basic.lean), [`TFT/Frobenius.lean`](../AxiomaticGW/TFT/Frobenius.lean), and [`TFT/Classification.lean`](../AxiomaticGW/TFT/Classification.lean), principally `TopologicalCorrelatorTheory`, `CommFrobeniusAlgebra.toTopologicalCorrelatorTheory`, and the product and round-trip theorems. The geometric oriented bordism category itself is deliberately not formalized.
- [Finite-labelled correlators](mathematics/M02TwoDimensionalTFT.md#2-finite-labelled-correlators) correspond to [`TFT/FiniteProduct.lean`](../AxiomaticGW/TFT/FiniteProduct.lean) and [`TFT/Correlator.lean`](../AxiomaticGW/TFT/Correlator.lean), principally `TFT.finiteProduct`, `CommFrobeniusAlgebra.correlator`, its normalization theorems, and `correlator_succ_eq_option_handle`.
- [Sewing identities](mathematics/M02TwoDimensionalTFT.md#3-sewing-identities) correspond to [`Linear/Contraction.lean`](../AxiomaticGW/Linear/Contraction.lean) and [`TFT/Sewing.lean`](../AxiomaticGW/TFT/Sewing.lean), principally `sewing_identity`, `selfContract_correlator`, and `pairContract_correlator`.
- [Topological CohFT viewpoint](mathematics/M02TwoDimensionalTFT.md#4-topological-cohft-viewpoint) corresponds to [`Combinatorics/StableArity.lean`](../AxiomaticGW/Combinatorics/StableArity.lean) and [`CohFT/Topological.lean`](../AxiomaticGW/CohFT/Topological.lean), principally `StableArity`, `TopologicalCohFT`, and the two `toTopologicalCohFT` constructions.
- Concrete correlator computations are collected in [`TFT/Examples.lean`](../AxiomaticGW/TFT/Examples.lean).

## M3. Stable curves and gluing

**Mathematical note:** [M3. Stable curves and gluing](mathematics/M03StableCurvesAndGluing.md).

- [Stable marked curves](mathematics/M03StableCurvesAndGluing.md#1-stable-marked-curves) are represented only through their numerical stable range in [`Combinatorics/StableArity.lean`](../AxiomaticGW/Combinatorics/StableArity.lean). The moduli stacks themselves are not constructed.
- [Primitive maps](mathematics/M03StableCurvesAndGluing.md#2-primitive-maps) and the [abstract cohomology system](mathematics/M03StableCurvesAndGluing.md#3-abstract-cohomology-system) correspond to [`CohFT/StableCurve.lean`](../AxiomaticGW/CohFT/StableCurve.lean), principally `EvenGradedAlgebra`, `StableCurveCohomology`, `GenusZeroGeometry`, `ConnectedDegreeZero`, and their degree and coherence fields.
- The constant degree-zero realization and acceptance path are implemented in [`CohFT/Constant.lean`](../AxiomaticGW/CohFT/Constant.lean) and exercised through [`AxiomaticGWTest/Basic.lean`](../AxiomaticGWTest/Basic.lean).
- [Stable graphs](mathematics/M03StableCurvesAndGluing.md#4-stable-graphs), arbitrary iterated gluing, and independence of contraction order are deferred by design decision D9 and do not yet have source modules.

## M4. Full unital CohFT

**Mathematical note:** [M4. Full unital CohFT](mathematics/M04FullUnitalCohFT.md).

- [State space and classes](mathematics/M04FullUnitalCohFT.md#1-state-space-and-classes), [relabelling and gluing](mathematics/M04FullUnitalCohFT.md#2-relabelling-and-gluing), and [unit and normalization](mathematics/M04FullUnitalCohFT.md#3-unit-and-normalization) correspond to [`CohFT/Basic.lean`](../AxiomaticGW/CohFT/Basic.lean), principally `CohFT` and `GradedCohFT`.
- [Underlying Frobenius algebra](mathematics/M04FullUnitalCohFT.md#4-underlying-frobenius-algebra) corresponds to [`CohFT/GenusZero.lean`](../AxiomaticGW/CohFT/GenusZero.lean) and [`CohFT/Frobenius.lean`](../AxiomaticGW/CohFT/Frobenius.lean), principally `CohFT.toGenusZeroCohFT`, `GenusZeroCohFT.product`, `pairing_products_wdvv`, `product_assoc`, and `toCommFrobeniusAlgebra`.
- [Topological part and genus zero](mathematics/M04FullUnitalCohFT.md#5-topological-part-and-genus-zero) correspond to [`CohFT/TopologicalPart.lean`](../AxiomaticGW/CohFT/TopologicalPart.lean) and [`CohFT/Classification.lean`](../AxiomaticGW/CohFT/Classification.lean), principally `CohFT.topologicalPart` and `TopologicalCohFT.classification`.

## Planned phases

M5-M10 have mathematical notes and roadmap entries but no production source modules yet. Add their mappings here only when the corresponding Lean API is implemented and verified; do not add speculative source paths or declarations.

## Maintenance rule

When a milestone changes the public mathematical API, update this map in the same change. Keep dated implementation and verification details in the [progress record](milestones/ImplementationProgress.md) rather than duplicating them here.
